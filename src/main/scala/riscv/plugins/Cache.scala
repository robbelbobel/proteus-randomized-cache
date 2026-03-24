package riscv.plugins

import riscv._
import spinal.core._
import spinal.lib._

object ReplacementPolicy extends SpinalEnum {
  val PLRU, RAN = newElement() // Pseudo-LRU, Random
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
    randomizedSetIndexing: Bool = True,
    replacementPolicy: ReplacementPolicy.E = ReplacementPolicy.RAN,
    skewApproach: SkewApproach.E = SkewApproach.LA,
    invalidTags: Int = 0, // Invalid Tags
    evictionPolicy: EvictionPolicy.E = EvictionPolicy.LE,
    delay: Int = 1
)(implicit config: Config)
    extends Plugin[Pipeline] {
  // Verify Security Options
  assert(skews >= 1, "Cache must exist out of 1 or more skews")
  assert(
    invalidTags < sets * ways * skews,
    "Invalidtags cannot be larger than the total amount of ways in the cache."
  )

  private val byteIndexBits = log2Up(config.xlen / 8)
  private val wordIndexBits = log2Up(config.memBusWidth / config.xlen)
  private val setIndexBits = log2Up(sets)

  // RNG
  private var rngBufferIndex: Int = 0

  // Initialize Key (4 Stages like CAESER)
  private val feistelStages = 4
  private val key = Vec.fill(feistelStages)(Reg(UInt(setIndexBits / 2 bits)))
  key(0) := 0x00
  key(1) := 0x01
  key(2) := 0x02
  key(3) := 0x03

  private case class CacheEntry() extends Bundle {
    val tag: UInt = UInt(config.xlen - (byteIndexBits + wordIndexBits + setIndexBits) bits)
    val value: UInt = UInt(config.memBusWidth bits)
    val age: UInt = UInt(log2Up(ways) bits) // Should only be needed in LRU replacement policies
    val valid: Bool = Bool()
  }

  case class WayResult() extends Bundle {
    val set: UInt = UInt(log2Up(sets) bits)
    val skew: UInt = UInt(log2Up(skews) bits)
    val way: UInt = UInt(log2Up(ways) bits)
  }

  private def getSetIndex(address: UInt): UInt = {
    if (randomizedSetIndexing == True && (setIndexBits % 2) == 0) {
      // Set Index Bits Must Be Divisible By 2 (Needed for Feistel Algorithm)
      assert(sets >= 2 && setIndexBits % 2 == 0);
      val half = setIndexBits / 2

      // 4-Stage Feistel-Network
      var L = address(byteIndexBits + wordIndexBits, half bits)
      var R = address(byteIndexBits + wordIndexBits + half, half bits)

      for (i <- 0 until feistelStages) {
        var temp = L
        L = R ^ key(i)
        R = temp
      }

      U(L ## R)
    } else {
      // Default to Standard Set-Associative Indexing
      address(byteIndexBits + wordIndexBits, setIndexBits bits)
    }
  }

  private def getTagBits(address: UInt): UInt = {
    address(byteIndexBits + wordIndexBits + setIndexBits until config.xlen)
  }

  // get all address bits that determine whether two addresses fall into the same cache line
  private def getSignificantBits(address: UInt): UInt = {
    U(getTagBits(address) ## getSetIndex(address))
  }

  private def connect(_s: Stage, internal: MemBus, external: MemBus): Unit = {
    val cacheArea = pipeline plug new Area {
      val rngService = pipeline.service[RngService]
      val rng = new RngIo
      rng.rdata_request := False // TODO: This should be handled by isSlave!!
      rng <> rngService.getRngBuffer(rngBufferIndex)

      private val totalWays: Int = ways * skews * sets

      private val idWidth = internal.config.idWidth
      private val maxId = UInt(idWidth bits).maxValue.intValue()

      private val cache =
        Vec.fill(sets)(Vec.fill(skews)(Vec.fill(ways)(RegInit(CacheEntry().getZero))))

      private val cacheHits = RegInit(UInt(config.xlen bits).getZero)
      private val cacheMisses = RegInit(UInt(config.xlen bits).getZero)
      private val forwardedLoads = RegInit(UInt(config.xlen bits).getZero)
      private val validTags =
        RegInit(UInt(config.xlen bits).getZero) // Tracks the amount of valid tags currently in this cache

      private val externalId = RegInit(UInt(external.config.idWidth bits).getZero)

      private val storeInCycle = Bool()
      storeInCycle := False

      private val outstandingPrefetches = RegInit(UInt(log2Up(maxPrefetches + 1) bits).getZero)
      private val incrementOutstandingPrefetches = Bool()
      private val decrementOutstandingPrefetches = Bool()
      incrementOutstandingPrefetches := False
      decrementOutstandingPrefetches := False

      // this logic is to avoid problems when incrementing and decrementing in the same cycle
      when(incrementOutstandingPrefetches && !decrementOutstandingPrefetches) {
        outstandingPrefetches := outstandingPrefetches + 1
      } elsewhen (!incrementOutstandingPrefetches && decrementOutstandingPrefetches) {
        outstandingPrefetches := outstandingPrefetches - 1
      }

      private def getSkewUsage(set: UInt, skew: UInt): UInt = {
        assert(skew < skews)
        assert(set < sets)

        // Count valid ways in provided skew
        val result = UInt(ways bits)
        result := 0
        for (i <- 0 until ways) {
          when(cache(set)(skew)(i).valid) {
            result := result + 1
          }
        }

        result
      }

      private def getCacheUsage(): UInt = {
        val max = sets * skews * ways
        val width = log2Up(max + 1)

        val acc = Reg(UInt(width bits)).init(0)

        acc := 0
        for (i <- 0 until sets) {
          for (j <- 0 until skews) {
            for (k <- 0 until ways) {
              when(cache(i)(j)(k).valid) {
                acc := acc + 1
              }
            }
          }
        }

        acc
      }
    
      private def getSkew(set: UInt): UInt = {
        assert(skews >= 2) // This function should only be called when multiple skews are used

        if (skewApproach == SkewApproach.RS) {
          // Random Selection
          val (rngValid, rngValue) = rng.get()
          assert(rngValid, "Invalid rng value generated")

          rngValue % skews
        } else {
          // Load Aware
          // Calculate usage of skews
          val usage = Vec.fill(skews)(UInt(log2Up(ways) bits))
          for (i <- 0 until skews) {
            usage(i) := getSkewUsage(set, i)
          }

          // Find skew with lowest usage
          val result = UInt(log2Up(skews) bits)
          result := 0
          for (i <- 0 until skews) {
            when(usage(i) < usage(result)) {
              result := i
            }
            when(usage(i) === usage(result)) {
              // todo: Randomness Here
            }
          }

          result
        }
      }

      private def oldestWay(set: UInt, skew: UInt): UInt = {
        val result = UInt(log2Up(ways) bits)
        result := 0

        if (evictionPolicy == EvictionPolicy.LE) {
          // Local Eviction
          for (i <- 0 until ways) {
            when(cache(set)(skew)(i).age === ways - 1 || !cache(set)(skew)(i).valid) {
              result := i
            }
          }
        }

        result
      }

      private def increaseAgesUpTo(set: UInt, oldest: UInt): Unit = {
        for (j <- 0 until skews) {
          for (i <- 0 until ways) {
            when(cache(set)(j)(i).age < oldest) {
              cache(set)(j)(i).age := cache(set)(j)(i).age + 1
            }
          }
        }
      }

      private def decreaseAgesUntil(set: UInt, youngest: UInt): Unit = {
        for (j <- 0 until skews) {
          for (i <- 0 until ways) {
            when(cache(set)(j)(i).age > youngest) {
              cache(set)(j)(i).age := cache(set)(j)(i).age - 1
            }
          }
        }
      }

      private def evictWayGlobal(): WayResult = {
        // Evicts a Way Globally
        val result = WayResult()

        if(replacementPolicy == ReplacementPolicy.PLRU) {
          result.way := U(0).resized
          // TODO: Least Recently Used Approach
        } else {
          // Random Approach
          val (rngValid, rngValue) = rng.get()
          assert(rngValid, "Received an invalid rng value") // TODO: Handle invalid rng value

          result.way := rngValue(log2Up(ways) - 1 downto 0).resized
          result.skew := rngValue(log2Up(ways) + log2Up(skews) - 1 downto log2Up(ways)).resized
          result.set := rngValue(log2Up(sets) + log2Up(ways) + log2Up(skews) - 1 downto log2Up(ways) + log2Up(skews)).resized
        }

        result
      }

      private def evictWayLocal(setIndex: UInt, skew: UInt): UInt = {
        // Evicts a Way for a Given Set and Skew
        if (replacementPolicy == ReplacementPolicy.PLRU) {
          // Least Recently Used Approach
          val way = oldestWay(setIndex, skew)
          cache(setIndex)(skew)(way).valid := False
          increaseAgesUpTo(setIndex, ways - 1)

          return way
        } else {
          // Random Approach
          val (rngValid, rngValue) = rng.get()
          assert(rngValid, "Received an invalid rng value") // TODO: Handle invalid rng value

          val way = (rngValue % ways).resized
          cache(setIndex)(skew)(way).valid := False

          return way
        }
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
        val setIndex = getSetIndex(address)
        val tag = getTagBits(address)
        val skew = if (skews >= 2) getSkew(setIndex) else U(0, log2Up(skews) bits)

        outstandingLoads(external.rsp.id).pending := False
        outstandingLoads(external.rsp.id).storeInvalidated := False
        // make sure we don't insert values that have been overwritten with a store
        // either before or in the current cycle
        when(
          !outstandingLoads(external.rsp.id).storeInvalidated &&
            cacheable(address) &&
            !(storeInCycle &&
              getSignificantBits(address) === getSignificantBits(internal.cmd.address))
        ) {
          var stored = False
          var evict = False
          for (i <- 0 until ways) {
            when(cache(setIndex)(skew)(i).valid === False) {
              // Free Entry Found -> Insert Here
              cache(setIndex)(skew)(i).valid := True
              cache(setIndex)(skew)(i).tag := tag
              cache(setIndex)(skew)(i).value := external.rsp.rdata
              cache(setIndex)(skew)(i).age := U(0).resized
              stored = True

              validTags := validTags + 1 // May Trigger an Eviction
              if (replacementPolicy == ReplacementPolicy.PLRU) {
                increaseAgesUpTo(setIndex, ways - 1) // Increase Ages when PLRU is used
              }
            }
          }

          when(stored === False) {
            // No Free Ways -> Evict Way and use evicted entry
            val way = evictWayLocal(setIndex, skew)

            cache(setIndex)(skew)(way).valid := True
            cache(setIndex)(skew)(way).tag := tag
            cache(setIndex)(skew)(way).value := external.rsp.rdata
            cache(setIndex)(skew)(way).age := U(0).resized
          }

          when(getCacheUsage() + invalidTags > totalWays) {
            // Valid Tag count has been exceeded
            if (evictionPolicy == EvictionPolicy.LE) {
              // Local Eviction
              evictWayLocal(setIndex, skew)
            } else {
              // Global Eviction
              evictWayGlobal()
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
        val set = cache(getSetIndex(address))
        val tag = getTagBits(address)
        val result = Flow(WayResult())
        result.setIdle()
        for (j <- 0 until skews) {
          for (i <- 0 until ways) {
            when(set(j)(i).valid && set(j)(i).tag === tag) {
              val wayResult = WayResult()
              wayResult.set := getSetIndex(address)
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
              val setIndex = getSetIndex(prefetchAddress)
              val tagBits = getTagBits(prefetchAddress)

              val alreadyPending = False

              // find out if a load request for the given address is already pending
              for (i <- 0 until outstandingLoads.length) {
                val load = outstandingLoads(i)
                when(
                  getSignificantBits(load.address) === U(
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
        val setIndex = getSetIndex(address)
        val cacheSet = cache(setIndex)
        val tagBits = getTagBits(address)

        when(targetWay.valid) {
          cacheSet(targetWay.payload.skew)(targetWay.payload.way).age := U(0).resized
          increaseAgesUpTo(setIndex, cacheSet(targetWay.payload.skew)(targetWay.payload.way).age)
          returnFromCache(cacheSet(targetWay.payload.skew)(targetWay.payload.way))
        } otherwise {
          val alreadyPending = False
          for (i <- 0 until outstandingLoads.length) {
            val load = outstandingLoads(i)
            when(
              getSignificantBits(load.address) === U(
                tagBits ## setIndex
              ) && load.pending && !load.storeInvalidated
            ) {
              alreadyPending := True
              // if the load is already pending but result not yet received: mark it to be forwarded + increase cache misses
              when(
                !(external.rsp.valid && getSignificantBits(load.address) === getSignificantBits(
                  outstandingLoads(external.rsp.id).address
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
        val indexBits = getSetIndex(internal.cmd.address)
        val tagBits = getTagBits(internal.cmd.address)

        if (internal.config.readWrite) {
          when(internal.cmd.write) {
            storeInCycle := True
            // write command: invalidates line and forwards to external bus
            for (j <- 0 until skews) {
              for (i <- 0 until ways) {
                when(cache(indexBits)(j)(i).tag === tagBits) {
                  cache(indexBits)(j)(i).valid := False
                  validTags := validTags - 1 // Decrease Valid Tag Counter
                  cache(indexBits)(j)(i).age := ways - 1
                  decreaseAgesUntil(indexBits, cache(indexBits)(j)(i).age)
                }
              }
            }

            for (i <- 0 until outstandingLoads.length) {
              when(
                getSignificantBits(outstandingLoads(i).address) === getSignificantBits(
                  internal.cmd.address
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
  override def setup(): Unit = {
    // RNG
    val rngService = pipeline.service[RngService]
    rngBufferIndex = rngService.registerRngBuffer(new RngFifo())
  }

  override def build(): Unit = {
    busFilter(connect)
  }
}
