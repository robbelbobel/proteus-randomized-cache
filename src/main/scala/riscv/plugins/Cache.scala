package riscv.plugins

import riscv._
import spinal.core._
import spinal.lib._
import riscv.BaseIsa.RV32E.xlen
import scala.util.Random
import spinal.core.sim.SimDataPimper

object ReplacementPolicy extends SpinalEnum {
  val LRU, RAN = newElement() // Pseudo-LRU, Random
}

object SkewApproach extends SpinalEnum {
  val RS, LA = newElement() // Random Selection, Load Aware
}

object EvictionPolicy extends SpinalEnum {
  val LE, GE = newElement() // Local Eviction, Global Eviction
}

class Cache(
    sets: Int,
    ways: Int,
    skews: Int,
    busFilter: ((Stage, MemBus, MemBus) => Unit) => Unit,
    prefetcher: Option[PrefetchService] = None,
    maxPrefetches: Int = 1,
    cacheable: (UInt => Bool) = (_ => True),
    replacementPolicy: ReplacementPolicy.E = ReplacementPolicy.LRU,
    skewApproach: SkewApproach.E = SkewApproach.LA,
    invalidTags: Int = 0, // Invalid Tags
    evictionPolicy: EvictionPolicy.E = EvictionPolicy.GE,
    delay: Int = 1
)(implicit config: Config)
    extends Plugin[Pipeline] {
  // Verify Security Options
  assert(skews >= 1, "Cache must exist out of 1 or more skews")
  assert(
    invalidTags < sets * ways * skews,
    "InvalidTags cannot be larger than the total amount of ways in the cache."
  )

  private val byteIndexBits = log2Up(config.xlen / 8)
  private val wordIndexBits = log2Up(config.memBusWidth / config.xlen)
  private val setBits = log2Up(sets)

  // Tag bits (Needed for Feistel Algorithm)
  assert((config.xlen - byteIndexBits - wordIndexBits) % 2 == 0, "Tag bits must be divisable by 2")

  private case class CacheEntry() extends Bundle {
    val tag: UInt = UInt(config.xlen - (byteIndexBits + wordIndexBits) bits)
    val value: UInt = UInt(config.memBusWidth bits)
    val age: UInt = UInt(log2Up(ways) bits)
    val valid: Bool = Bool()
  }

  case class WayResult() extends Bundle {
    val set: UInt = UInt(log2Up(sets) bits)
    val skew: UInt = UInt(log2Up(skews) bits)
    val way: UInt = UInt(log2Up(ways) bits)
  }

  class SkewUsage() extends Bundle {
    val skew: UInt = UInt(log2Up(skews) bits)
    val usage: UInt = UInt(log2Up(ways + 1) bits)
  }

  private val feistelStages = 4

  private def getSetIndex(address: UInt, key: Vec[UInt]): UInt = {
    val half = (config.xlen - byteIndexBits - wordIndexBits) / 2

    // 4-Stage Feistel-Network
    var L = address(byteIndexBits + wordIndexBits, half bits)
    var R = address(byteIndexBits + wordIndexBits + half, half bits)

    for (i <- 0 until feistelStages) {
      val F = R ^ key(i)
      var temp = L ^ F
      L = R
      R = temp
    }

    (L ## R).asUInt(setBits - 1 downto 0)
  }

  private def getTagBits(address: UInt): UInt = {
    address(byteIndexBits + wordIndexBits until config.xlen)
  }

  // get all address bits that determine whether two addresses fall into the same cache line
  private def getSignificantBits(address: UInt, key: Vec[UInt]): UInt = {
    U(getTagBits(address) ## getSetIndex(address, key))
  }

  private def connect(_s: Stage, internal: MemBus, external: MemBus): Unit = {
    val cacheArea = pipeline plug new Area {
      // Initialize Key (4 Stages like CAESER)
      private val key = Vec.fill(feistelStages)(Reg(UInt((config.xlen - byteIndexBits - wordIndexBits) / 2 bits)))

      for (i <- 0 until feistelStages) {
        key(i) := scala.util.Random.nextInt(1 << ((config.xlen - byteIndexBits - wordIndexBits) / 2))
      }

      private val totalWays: Int = ways * skews * sets

      private val idWidth = internal.config.idWidth
      private val maxId = UInt(idWidth bits).maxValue.intValue()

private val cache =
        Vec.fill(skews)(Vec.fill(sets)(Vec.fill(ways)(RegInit(CacheEntry().getZero))))

      private val cacheHits = RegInit(UInt(config.xlen bits).getZero)
      private val cacheMisses = RegInit(UInt(config.xlen bits).getZero)
      private val forwardedLoads = RegInit(UInt(config.xlen bits).getZero)
      private val externalId = RegInit(UInt(external.config.idWidth bits).getZero)

      private val storeInCycle = Bool()
      storeInCycle := False

      private val outstandingPrefetches = RegInit(UInt(log2Up(maxPrefetches + 1) bits).getZero)
      private val incrementOutstandingPrefetches = Bool()
      private val decrementOutstandingPrefetches = Bool()
      incrementOutstandingPrefetches := False
      decrementOutstandingPrefetches := False

      // RNG
      private val rngState =
        RegInit(U(BigInt(config.xlen * 2, scala.util.Random), config.xlen * 2 bits))
      private val rngMutliplier = BigInt(config.xlen * 2, scala.util.Random)
      private val rngIncrement = BigInt(config.xlen * 2, scala.util.Random) | 1 // odd!

      private def rotr32(x: UInt, r: UInt): UInt = {
        (x >> r).resize(config.xlen bits) | (x << (config.xlen - r)).resize(config.xlen bits)
      }

      private def pcg32(): UInt = {
        val count = rngState >> 59 // 64 - 59 = 5 -> 5 bit rotation (32 bit possible rotations)

        val x = rngState ^ (rngState >> 18).resize(config.xlen * 2 bits) // 18 = (64 - 27)/2
        rngState := (rngState * rngMutliplier + rngIncrement).resize(config.xlen * 2 bits)

        rotr32((x >> 27).resize(config.xlen bits), count)
      }

      private var rngOutput = pcg32();

      // Valid Tag Counter
      private val tagEvicted = Bool() // Through Eviction
      private val tagInvalidated = Bool() // Through e.g. write
      private val tagInserted = Bool() // Newly Inserted Tags (former invalid tags)
      private val validTags = RegInit(UInt(log2Up(sets * skews * ways + 1) bits).getZero)

      tagEvicted := False
      tagInvalidated := False
      tagInserted := False
      validTags := validTags - tagEvicted.asUInt.resized - tagInvalidated.asUInt.resized + tagInserted.asUInt.resized

      private val lastInsertionSkew = RegInit(UInt(log2Up(skews) bits).getZero) 
      private val lastInsertionSet = RegInit(UInt(log2Up(sets) bits).getZero) 

      if (invalidTags > 0) {
        when (validTags > totalWays - invalidTags) {
          if (evictionPolicy == EvictionPolicy.LE) {
            // Local Eviction
            evictWayLocal()
          }else {
            // Global Eviction
            evictWayGlobal()
          }
        }
      }

      // this logic is to avoid problems when incrementing and decrementing in the same cycle
      when(incrementOutstandingPrefetches && !decrementOutstandingPrefetches) {
        outstandingPrefetches := outstandingPrefetches + 1
      } elsewhen (!incrementOutstandingPrefetches && decrementOutstandingPrefetches) {
        outstandingPrefetches := outstandingPrefetches - 1
      }

      private def getSkewUsage(set: UInt, skew: UInt): UInt = {
        // Count valid ways in provided skew
        val counts = (0 until ways).map { i =>
          cache(skew)(set)(i).valid.asUInt.resized
        }

        counts.reduceBalancedTree((_ + _)).resize(log2Up(ways + 1) bits)
      }

      private def getSkew(set: UInt): UInt = {
        assert(skews >= 2) // This function should only be called when multiple skews are used

        if (skewApproach == SkewApproach.RS) {
          // Random Selection
          (rngOutput % skews).resize(log2Up(skews) bits)
        } else {
          // Load Aware
          // Calculate usage of skews
          val usage = (0 until skews).map { i =>
            val s = new SkewUsage()
            s.skew := U(i, log2Up(skews) bits)
            s.usage := getSkewUsage(set, U(i, log2Up(skews) bits))
            s
          }

          // Find skew with lowest usage
          val best = usage.reduceBalancedTree((a, b) =>
            Mux(a.usage === b.usage, (Mux(rngOutput(0), a, b)), Mux(a.usage < b.usage, a, b))
          )

          best.skew
        }
      }

      private def oldestWay(skew: UInt, set: UInt): WayResult = {
        val result = WayResult()
        result.set := set
        result.skew := skew
        result.way := 0

        for (i <- 0 until ways) {
          when(cache(skew)(set)(i).age === (ways - 1) || !cache(skew)(set)(i).valid) {
            result.way := i
          }
        }

        result
      }

      private def increaseAgesUpTo(skew: UInt, set: UInt, oldest: UInt): Unit = {
        for (i <- 0 until ways) {
          when(cache(skew)(set)(i).age < oldest) {
            cache(skew)(set)(i).age := (cache(skew)(set)(i).age + 1).resize(log2Up(ways) bits)
          }
        }
      }

      private def decreaseAgesUntil(skew: UInt, set: UInt, youngest: UInt): Unit = {
        for (i <- 0 until ways) {
          when(cache(skew)(set)(i).age > youngest) {
            cache(skew)(set)(i).age := (cache(skew)(set)(i).age - 1).resize(log2Up(ways) bits)
          }
        }
      }

      private def evictWayGlobal(): WayResult = {
        // Evicts a Way Globally -> Choose Randomly
        val result = WayResult()

        result.way := rngOutput(log2Up(ways) - 1 downto 0).resized
        result.skew := rngOutput(log2Up(ways) + log2Up(skews) - 1 downto log2Up(ways)).resized
        result.set := rngOutput(
          log2Up(sets) + log2Up(ways) + log2Up(skews) - 1 downto log2Up(ways) + log2Up(skews)
        ).resized

        // Evict Entry
        when(cache(result.skew)(result.set)(result.way).valid) {
          tagEvicted := True
        }

        if (replacementPolicy == ReplacementPolicy.LRU) {
          decreaseAgesUntil(result.skew, result.set, cache(result.skew)(result.set)(result.way).age)
        }

        cache(result.skew)(result.set)(result.way).valid := False

        result
      }

      private def evictWayLocal(): WayResult = {
        // Randomly Evict Way Locally
        val result = WayResult()

        result.way := rngOutput(log2Up(ways) - 1 downto 0).resized
        result.skew := lastInsertionSkew
        result.set := lastInsertionSet

        // Evict Entry
        when(cache(result.skew)(result.set)(result.way).valid) {
          tagEvicted := True
        }

        if (replacementPolicy == ReplacementPolicy.LRU) {
          decreaseAgesUntil(result.skew, result.set, cache(result.skew)(result.set)(result.way).age)
        }

        cache(result.skew)(result.set)(result.way).valid := False

        result
      }

      private val sendingImmediateCmd = Bool()
      private val sendingBufferedCmd = Reg(Bool()).init(False)
      private val cmdBuffer = Reg(MemBusCmd(internal.config))

      // rsp sending buffer
      private val sendingRsp = Bool()
      sendingRsp := False
      private val alreadySendingRsp = Reg(Bool()).init(False)
      private val rspBuffer = Reg(MemBusRsp(internal.config))
      private val returningCache = Reg(Bool()).init(False)

      // Delay cache response with a fixed delay
      // Note that a minimal delay of 1 clock cycle is required to prevent
      // combinatorial loops in case of multiple dbus filters.
      private val internalRspBuffer = Stream(MemBusRsp(internal.config))
      internal.rsp << internalRspBuffer.delay(delay)

      // initial state: not sending or acknowledging anything
      internalRspBuffer.valid := False
      internalRspBuffer.payload.assignDontCare()
      internal.cmd.ready := False
      external.cmd.valid := False
      external.cmd.payload.assignDontCare()
      external.rsp.ready := False

      sendingImmediateCmd := False

      private case class OutstandingTracker() extends Bundle {
        val address: UInt = UInt(config.xlen bits)
        val storeInvalidated: Bool = Bool()
        val pending: Bool = Bool()
        val isPrefetch: Bool = Bool()
        val internalIds: Bits = Bits(1 << internal.config.idWidth bits)
      }

      private val outstandingLoads = Vec.fill(maxId + 1)(RegInit(OutstandingTracker().getZero))

      private def forwardRspToInternal(): Unit = {
        sendingRsp := True
        internalRspBuffer.valid := True

        internalRspBuffer.rdata := external.rsp.rdata
        // the index of 1's in internalIds indicate to which internal ids the response should be forwarded
        val internalId = OHToUInt(OHMasking.first(outstandingLoads(external.rsp.id).internalIds))
        internalRspBuffer.id := internalId
        when(internalRspBuffer.ready) {
          // set the bit to 0 once it has been forwarded
          outstandingLoads(external.rsp.id).internalIds(internalId) := False
        }
      }

      private def insertRspInCache(address: UInt): Unit = {
        val hit = wayForAddress(address)

        when(hit.valid && cache(hit.payload.skew)(hit.payload.set)(hit.payload.way).valid) {
          // Rsp already stored in cache -> Decrease Age Only
          if (replacementPolicy == ReplacementPolicy.LRU) {
            increaseAgesUpTo(
              hit.payload.skew,
              hit.payload.set,
              cache(hit.payload.skew)(hit.payload.set)(hit.payload.way).age
            )

            cache(hit.payload.skew)(hit.payload.set)(hit.payload.way).age := U(0).resized
          }

          cache(hit.payload.skew)(hit.payload.set)(hit.payload.way).value := external.rsp.rdata
        }

        outstandingLoads(external.rsp.id).pending := False
        outstandingLoads(external.rsp.id).storeInvalidated := False
        // make sure we don't insert values that have been overwritten with a store
        // either before or in the current cycle
        when(
          !outstandingLoads(external.rsp.id).storeInvalidated &&
            cacheable(address) &&
            !(storeInCycle &&
              getSignificantBits(address, key) === getSignificantBits(internal.cmd.address, key)) &&
            !hit.valid
        ) {
          val setIndex = getSetIndex(address, key)
          val tag = getTagBits(address)
          val skew = if (skews >= 2) getSkew(setIndex) else U(0, log2Up(skews) bits)

          val found = Bool()
          found := False

          val freeidx = UInt(log2Up(ways) bits)
          freeidx := 0

          for (i <- 0 until ways) {
            when(!cache(skew)(setIndex)(i).valid) {
              freeidx := i
              found := True
            }
          }

          when(found) {
            if (replacementPolicy == ReplacementPolicy.LRU) {
              // Increase Ages when LRU is used
              increaseAgesUpTo(
                skew,
                setIndex,
                ways - 1
              )
            }

            // Free Entry Found -> Insert Here
            cache(skew)(setIndex)(freeidx).valid := True
            cache(skew)(setIndex)(freeidx).tag := tag
            cache(skew)(setIndex)(freeidx).value := external.rsp.rdata
            cache(skew)(setIndex)(freeidx).age := U(0).resized

            // Updated TagInserted
            tagInserted := True

            if (invalidTags > 0) {
              lastInsertionSet := setIndex
              lastInsertionSkew := skew
            }
          }

          when(!found) {
            // No Free Ways -> Use Replacement Policy
            if (replacementPolicy == ReplacementPolicy.LRU) {
              // Least Recently Used Approach
              val wayResult = oldestWay(skew, setIndex)

              increaseAgesUpTo(skew, setIndex, cache(wayResult.skew)(setIndex)(wayResult.way).age)

              cache(wayResult.skew)(setIndex)(wayResult.way).valid := True
              cache(wayResult.skew)(setIndex)(wayResult.way).tag := tag
              cache(wayResult.skew)(setIndex)(wayResult.way).value := external.rsp.rdata
              cache(wayResult.skew)(setIndex)(wayResult.way).age := U(0).resized
            } else {
              // Random Approach
              val wayResult = WayResult()

              wayResult.set := setIndex
              wayResult.way := rngOutput(log2Up(ways) downto 0).resized // Prevent assignment overlap
              wayResult.skew := skew

              cache(wayResult.skew)(setIndex)(wayResult.way).valid := True
              cache(wayResult.skew)(setIndex)(wayResult.way).tag := tag
              cache(wayResult.skew)(setIndex)(wayResult.way).value := external.rsp.rdata
              cache(wayResult.skew)(setIndex)(wayResult.way).age := U(0).resized
            }
          }
        }

        external.rsp.ready := True
      }

      // handling an incoming result from the memory
      when(external.rsp.valid) {
        val address = outstandingLoads(external.rsp.id).address

        when(!alreadySendingRsp) {
          prefetcher foreach { pref =>
            when(outstandingLoads(external.rsp.id).isPrefetch) {
              // inform prefetcher of prefetch response from memory
              pref.notifyPrefetchResponseFromMemory(address, external.rsp.rdata)
              // subscract 1 from outstandingPrefetches
              decrementOutstandingPrefetches := True
            } otherwise {
              // inform prefetcher of load response from memory
              pref.notifyLoadResponseFromMemory(address, external.rsp.rdata)
            }
          }
        }

        when(outstandingLoads(external.rsp.id).internalIds === 0) {
          // store result in cache without forwarding
          insertRspInCache(address)
        } otherwise {
          // forward result and store in cache
          forwardRspToInternal()
          when(
            // when there is only one id left to forward, put result in cache and inform external bus we are done
            internalRspBuffer.ready && CountOne(outstandingLoads(external.rsp.id).internalIds) === 1
          ) {
            insertRspInCache(address)
            alreadySendingRsp := False
          } otherwise {
            alreadySendingRsp := True
          }
        }
      }

      private def returnFromCache(cacheLine: CacheEntry): Unit = {
        // result served from cache
        when(!returningCache) {
          cacheHits := cacheHits + 1
          internal.cmd.ready := True
          rspBuffer.id := internal.cmd.id
          rspBuffer.rdata := cacheLine.value
          when(!sendingRsp) {
            internalRspBuffer.valid := True
            internalRspBuffer.id := internal.cmd.id
            internalRspBuffer.rdata := cacheLine.value
            when(!internalRspBuffer.ready) {
              returningCache := True
            }
          } otherwise {
            returningCache := True
          }
        }
        // if buffer is currently full, we do not ack the cmd, it will stay on the bus for the next cycle
      }

      when(returningCache && !sendingRsp) {
        // when not forwarding rsp but have a stored cache hit, return that
        internalRspBuffer.valid := True
        internalRspBuffer.payload := rspBuffer
        when(internalRspBuffer.ready) {
          returningCache := False
        }
      }

      private def initiateCmdForwarding(): Unit = {
        when(!sendingBufferedCmd) {
          sendingImmediateCmd := True
          internal.cmd.ready := True
          external.cmd.valid := True

          cmdBuffer := external.cmd.payload

          external.cmd.address := internal.cmd.address
          external.cmd.id := externalId

          if (internal.config.readWrite) {
            external.cmd.write := internal.cmd.write
            external.cmd.wdata := internal.cmd.wdata
            external.cmd.wmask := internal.cmd.wmask

            when(!internal.cmd.write) {
              outstandingLoads(externalId).address := internal.cmd.address
              outstandingLoads(externalId).pending := True
              outstandingLoads(externalId).isPrefetch := False
              outstandingLoads(externalId).internalIds := B(0).resized
              outstandingLoads(externalId).internalIds(internal.cmd.id) := True
              externalId := externalId + 1
            }
          } else {
            outstandingLoads(externalId).address := internal.cmd.address
            outstandingLoads(externalId).pending := True
            outstandingLoads(externalId).isPrefetch := False
            outstandingLoads(externalId).internalIds := B(0).resized
            outstandingLoads(externalId).internalIds(internal.cmd.id) := True
            externalId := externalId + 1
          }
          when(!external.cmd.ready) {
            sendingBufferedCmd := True
          }
        }
      }

      when(sendingBufferedCmd) {
        external.cmd.valid := True
        external.cmd.payload := cmdBuffer
        when(external.cmd.ready) {
          sendingBufferedCmd := False
        }
      }

      private def wayForAddress(address: UInt): Flow[WayResult] = {
        val setIndex = getSetIndex(address, key)
        val tag = getTagBits(address)
        val result = Flow(WayResult())
        result.setIdle()
        for (j <- 0 until skews) {
          for (i <- 0 until ways) {
            when(cache(j)(setIndex)(i).valid && cache(j)(setIndex)(i).tag === tag) {
              val wayResult = WayResult()
              wayResult.set := getSetIndex(address, key)
              wayResult.skew := j
              wayResult.way := i
              result.push(wayResult)
            }
          }
        }

        result
      }

      prefetcher foreach { pref =>
        when(
          !sendingBufferedCmd && !sendingImmediateCmd && outstandingPrefetches < maxPrefetches && pref.hasPrefetchTarget
        ) {
          when(!outstandingLoads(externalId).pending) {
            // at this point the cache is ready to send a prefetch command to the memory
            // getNextPrefetchTarget should not be called before the cache is ready to send the command
            // otherwise the prefetch may get lost
            val prefetchAddress = pref.getNextPrefetchTarget

            when(cacheable(prefetchAddress)) {
              val targetWay = wayForAddress(prefetchAddress)
              val setIndex = getSetIndex(prefetchAddress, key)
              val tagBits = getTagBits(prefetchAddress)

              val alreadyPending = False

              // find out if a load request for the given address is already pending
              for (i <- 0 until outstandingLoads.length) {
                val load = outstandingLoads(i)
                when(
                  getSignificantBits(load.address, key) === U(
                    tagBits ## setIndex
                  ) && load.pending && !load.storeInvalidated
                ) {
                  alreadyPending := True
                }
              }
              when(!targetWay.valid && !alreadyPending) {
                // add 1 to outstandingPrefetches
                incrementOutstandingPrefetches := True

                externalId := externalId + 1

                external.cmd.valid := True
                external.cmd.address := prefetchAddress
                external.cmd.id := externalId
                cmdBuffer := external.cmd.payload

                outstandingLoads(externalId).address := prefetchAddress
                outstandingLoads(externalId).pending := True
                outstandingLoads(externalId).internalIds := B(0).resized
                outstandingLoads(externalId).isPrefetch := True

                when(!external.cmd.ready) {
                  sendingBufferedCmd := True
                }
              }
            }
          }
        }
      }

      private def getResult(address: UInt): Unit = {
        // inform prefetcher of load request
        prefetcher foreach { pref =>
          pref.notifyLoadRequest(address)
        }

        val targetWay = wayForAddress(address) // Flow[WayResult]
        val setIndex = getSetIndex(address, key)
        val cacheSet = cache(targetWay.skew)(setIndex)
        val tagBits = getTagBits(address)

        when(targetWay.valid) { // Conflict
          cacheSet(targetWay.payload.way).age := U(0).resized
          increaseAgesUpTo(
            targetWay.payload.skew,
            setIndex,
            cacheSet(targetWay.payload.way).age
          )

          returnFromCache(cacheSet(targetWay.payload.way))
        } otherwise {
          val alreadyPending = False
          for (i <- 0 until outstandingLoads.length) {
            val load = outstandingLoads(i)
            when(
              getSignificantBits(load.address, key) === U(
                tagBits ## setIndex
              ) && load.pending && !load.storeInvalidated
            ) {
              alreadyPending := True
              // if the load is already pending but result not yet received: mark it to be forwarded + increase cache misses
              when(
                !(external.rsp.valid && getSignificantBits(
                  load.address,
                  key
                ) === getSignificantBits(
                  outstandingLoads(external.rsp.id).address,
                  key
                ))
              ) {
                load.internalIds(internal.cmd.id) := True
                cacheMisses := cacheMisses + 1
                forwardedLoads := forwardedLoads + 1
                internal.cmd.ready := True
              }
            }
          }
          // there's no pending load for the same cache line and the bus id is free:
          when(!alreadyPending && !outstandingLoads(externalId).pending) {
            // initiateCmdForwarding() will only go through when !sendingBufferedCmd,
            // also add this check here to only increase cache misses once per request
            when(!sendingBufferedCmd) {
              // increase cache misses
              cacheMisses := cacheMisses + 1
            }

            // forward cmd to external bus
            initiateCmdForwarding()
          }
        }
      }

      // handling a load/write request from the CPU
      when(internal.cmd.valid) {
        val indexBits = getSetIndex(internal.cmd.address, key)
        val tagBits = getTagBits(internal.cmd.address)

        if (internal.config.readWrite) {
          when(internal.cmd.write) {
            storeInCycle := True
            // write command: invalidates line and forwards to external bus
            for (j <- 0 until skews) {
              for (i <- 0 until ways) {
                when(cache(j)(indexBits)(i).tag === tagBits) {
                  when(cache(j)(indexBits)(i).valid === True) {
                    // Invalidate Line
                    cache(j)(indexBits)(i).valid := False
                    // Update Tag Invalidated
                    tagInvalidated := True
                  }

                  // Maximize Age of Line
                  decreaseAgesUntil(U(j, log2Up(skews) bits), indexBits, cache(j)(indexBits)(i).age)
                  cache(j)(indexBits)(i).age := U(ways - 1, log2Up(ways) bits)
                }
              }
            }

            for (i <- 0 until outstandingLoads.length) {
              when(
                getSignificantBits(outstandingLoads(i).address, key) === getSignificantBits(
                  internal.cmd.address,
                  key
                ) && outstandingLoads(i).pending
              ) {
                outstandingLoads(i).storeInvalidated := True
              }
            }

            initiateCmdForwarding()
            // if currently forwarding a cmd, we do not ack it, it will stay on the bus for the next cycle
          } otherwise {
            getResult(internal.cmd.address)
          }
        } else {
          getResult(internal.cmd.address)
        }
      }
    }
    cacheArea.setName("cache_" + external.name)
  }

  /** PHASES * */
  override def build(): Unit = {
    busFilter(connect)
  }
}
