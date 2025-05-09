package xiangshan.cache.mmu

import org.chipsalliance.cde.config.Parameters
import chisel3._
import chisel3.util._
import xiangshan._
import xiangshan.cache.{HasDCacheParameters, MemoryOpConstants}
import utils._
import utility._
import freechips.rocketchip.diplomacy.{LazyModule, LazyModuleImp}
import freechips.rocketchip.tilelink._
import xiangshan.backend.fu.{PMPReqBundle, PMPRespBundle}

class mptReqBundle(implicit p: Parameters) extends XSBundle with MPTCacheParam {//mpt io interface req and resp , id is not used in ptw 
    val reqPA = UInt(ppnLen.W)
    val id = UInt(mptSourceWidth.W)
    val mptOnly = Bool()//1bit 控制逻辑，对mptchecker本身无用，用于mptchecker返回时的l2tlb 控制
}

class mptRespBundle(implicit p: Parameters) extends XSBundle with MPTCacheParam {
    val accessFault = Bool()
    val mptPerm = UInt(perms16Len.W)
    val contigousPerm = Bool()//仅对非H 拓展l0有效
    //表示连续8项perm一致； 无法做到像l0pte一样按照位压缩（8位 valididx），因为其gva->hpa映射关系并非线性(比如 gva->hpa的 ppn_low 不是1->1 2->2 而是 1->7 2->3)
    val permIsNAPOT = Bool()
    val id = UInt(mptSourceWidth.W)
    val mptLevel =  UInt(mptLevelLenUInt.W)//UInt level 
    val mptOnly = Bool()//1bit 控制逻辑，对mptchecker本身无用，用于mptchecker返回时的l2tlb 控制
    val reqPA = UInt(ppnLen.W)// in req to out req 
}

class SRAMTemplateMPT[T <: Data]
(
  gen: T, set: Int, way: Int = 1,
  shouldReset: Boolean = false, holdRead: Boolean = false,
  singlePort: Boolean = true, bypassWrite: Boolean = false,
  clkDivBy2: Boolean = false, readMCP2: Boolean = true
) extends Module {
  val io = IO(new Bundle {
    val r = Flipped(new SRAMReadBus(gen, set, way))
    val w = Flipped(new SRAMWriteBus(gen, set, way))
  })

  val wordType = UInt(gen.getWidth.W)
  val array = SyncReadMem(set, Vec(way, wordType))

  val (ren, wen) = (io.r.req.valid, io.w.req.valid)
  val realRen = ren && !wen// delay 1 gate

  val setIdx =  io.w.req.bits.setIdx
  val wdata = VecInit((io.w.req.bits.data).map(_.asTypeOf(wordType)))
  val waymask =  io.w.req.bits.waymask.getOrElse("b1".U)
  when (wen) { array.write(setIdx, wdata, waymask.asBools)}

  val raw_rdata = array.read(io.r.req.bits.setIdx, realRen)// 

  val mem_rdata = raw_rdata
  val rdata = mem_rdata.map(_.asTypeOf(gen))

  io.r.resp.data := VecInit(rdata)
  io.r.req.ready := !wen 
  io.w.req.ready := true.B

}

class PLRUOH(log_ways: Int) extends Module {
        val wayNum = 1<< log_ways
        val io = IO(new Bundle {
        val  access = Flipped(ValidIO(UInt(wayNum.W)))
        val replace = Output(UInt(wayNum.W))
        val upperCom = Output(Bool())
    }) 
    if(log_ways==0){   
        io.replace:= 1.U//OH 1 is b0
        io.upperCom := false.B // the tool is not happy when assigned to Dontcare
    } else if( log_ways==1){//delay 1 gate 
        val changed = io.access.bits(1) || io.access.bits(0) 
        // 01 will let state points to right 10 to left entry, 00 will disable state input,if input freezes, i.e. same access value with valid for more than 1 clk, the state will not change,great
        io.upperCom := changed 
        val state= RegEnable( io.access.bits(0), false.B,io.access.valid && changed) // OH last bit indicates the next state 01 state 1, 10 state 0 
        io.replace:= Cat(state, ~state) //replace state 1 : 10, state 0 01 opposite of the direction iof input
    } else {
        val top = wayNum
        val mid = 1<<(log_ways-1)
        val plruleft = Module(new PLRUOH(log_ways-1))//gen left and right entry
        plruleft.io.access.bits := io.access.bits(top-1, mid)
        plruleft.io.access.valid := io.access.valid

        val plruright = Module(new PLRUOH(log_ways-1))
        plruright.io.access.bits := io.access.bits(mid-1, 0)
        plruright.io.access.valid := io.access.valid

        val changed = plruleft.io.upperCom || plruright.io.upperCom
        val state= RegEnable( plruright.io.upperCom , false.B,io.access.valid && changed) // OH last bit indicates the next state 01 state 1, 10 state 0 
        io.upperCom := changed
        val leftreplace = (Fill(plruleft.wayNum,state) & plruleft.io.replace)
        val rightreplace =  (Fill(plruleft.wayNum,!state) & plruright.io.replace)//replace state 1 : 10, state 0 01
        io.replace:= Cat(leftreplace, rightreplace) 
    }
}
class PLRUOHSet(sets_log2: Int, log_ways: Int) extends Module  {
    val wayNum =1<< log_ways
    val setNum =1<< sets_log2 
    val io = IO(new Bundle {
    val  access = Flipped(ValidIO(UInt(wayNum.W)))
    val replace = Output(UInt(wayNum.W))
    val idx = Input(UInt(sets_log2.W))
    })

    val plruSet = Array.fill(setNum)(Module(new PLRUOH(log_ways)).io)
    val outputArray = Wire(Vec(setNum,UInt(wayNum.W)))
    val hitArray = Wire(Vec(setNum,Bool()))
    
    for (i <- 0 until setNum) {
      val Idxhit = (i.U === io.idx)
      hitArray(i) := Idxhit
      plruSet(i).access.bits := io.access.bits
      plruSet(i).access.valid := io.access.valid & Idxhit 
      outputArray(i):= plruSet(i).replace 
    }
    io.replace := Mux1H(hitArray,outputArray)     //better readablity, select replace based on hit idx   
            
            //select plru with idx, is this a demux? ans: it is
            //outputArray(i):= (Fill(setNum,Idxhit) & plruSet(i).replace)}// a switch to 0 or repalce based on idxhit
       // io.replace:= outputArray.reduce(_|_) //maybe not ideal,better self decide what kind of logic is used here                              
           // outputArray(i):=  plruSet(i).replace}
    //io.replace:= outputArray(io.idx)
} 


class mptData (implicit p: Parameters) extends XSBundle with MPTCacheParam {
    val data =  UInt(perms16Len.W) 
    def apply(data:UInt) :Unit={
        this.data:= data//zero extended 
    }
    def getPPN : UInt ={//get PPN
        this.data(ppnLen-1,0)
    }
    def getAddr(offset: UInt):UInt={
        Cat(this.getPPN,Cat(offset,0.U(3.W)))//2|3 byte =64bit
    } 
    def extractPerm(select: UInt): (UInt) = {//extract XWR using 4bit offset
    // cal start end and extract
        (this.data>>(select*3.U))(2,0)// not quite sure what kind of crap will be synthesized. I meant it to be a binary mux
    }
}

class mptEntry (implicit p: Parameters) extends XSBundle with MPTCacheParam {
    val N = Bool()
    val data = new mptData()
    val L= Bool()
    val V= Bool()
    def apply(sMEMResp:UInt):Unit={
        this.V:= (sMEMResp(0)===1.U)
        this.L:= (sMEMResp(1)===1.U)
        this.N:= (sMEMResp(63)===1.U)
        this.data.apply(sMEMResp(57,10))//xiangshan only support 48bit PA, so PPN only needs 36
    }
    def isValid:Bool={
        this.V
    }
    
    def isLeaf:Bool={
        this.L
    }

    def getAddr(offset: UInt):UInt={
        this.data.getAddr(offset)
 
    }
}


class mptCacheTag ( tagLen: Int, isSp:Boolean = false, isL0:Boolean = false) (implicit p: Parameters) extends XSBundle with MPTCacheParam {//<=
    //val sdid = if(SDID_cache_store_en) Some(UInt(SDIDLen.W)) else None //6.W 没用
    if(!isL0){val valid = Bool()}
    val tag = UInt(tagLen.W)
    val level = Option.when(isSp)(UInt((mptLevelLenOH-1).W))//sp can not be l0   
    val valid = Bool()
    def hit(ppn: UInt ): Bool={
        tag === ppn(ppnLen-1,ppnLen-tagLen)//tag =5, (47,43)
    }
    def hitSp (ppn: UInt ): Bool ={
        val hitL3 = (this.tag(tagLen-1,tagLen-mptL3TagLen) === ppn(ppnLen-1,ppnLen-mptL3TagLen))//tag =5, (47,43)
        val hitL2 = (this.tag(tagLen-1,tagLen-mptL2TagLen)  === ppn(ppnLen-1,ppnLen-mptL2TagLen))
        val hitL1 = (this.tag === ppn(ppnLen-1,ppnLen-tagLen)) 
        val hotVal = Mux1H(this.level.get, Seq(hitL3,hitL2, hitL1))//it is a tuple scala> 1 -> 2 res0: (Int, Int) = (1,2)
        hotVal 
    }
}
class mptCacheData( isPerms: Boolean= false)  (implicit p: Parameters) extends XSBundle with MPTCacheParam {
    val data = if(isPerms) UInt(perms16Len.W)  else UInt(ppnLen.W) //36.W
    def extractPerm(select: UInt): (UInt) = {//extract XWR using 4bit offset
    // cal start end and extract
    require(isPerms ,"extractPerm is only valid when isPerms is true")
    (this.data>>(select*3.U))(2,0)// not quite sure what kind of crap will be synthesized. I meant it to be a binary mux
    }
}

class mptCacheL0(implicit p: Parameters)  extends XSBundle with MPTCacheParam {
    val cacheData   = new mptCacheData(isPerms=true)
    val tag         = new mptCacheTag(tagLen = mptL0TagLen,isL0 = true )
}

class mptCacheReq (implicit p: Parameters) extends XSBundle with MPTCacheParam {
    val mptOnly = Bool()
    val reqPA= UInt(PAddrBits.W)
    val source = UInt(mptSourceWidth.W)
}
class MPTPipe (implicit p: Parameters) extends mptCacheReq { 
    val dataValid= Bool() 
    val flushCache =Bool()
}  

class refillBundle(implicit p: Parameters)  extends XSBundle with MPTCacheParam {
        val level = UInt(mptLevelLenOH.W)
        val PA= UInt((PAddrBits- MptOff).W)
        val refillData = new mptData()
        //val entryError = Bool()
        val isLeafMpte =Bool() // is leaf? decide what cache is refilled
    }
class MPTCacheIO(implicit p: Parameters) extends MMUIOBaseBundle with MPTCacheParam{
    val req = Flipped(DecoupledIO(new mptCacheReq()))

    val respHit = ValidIO(new Bundle {// source is waiting for cache to resp
        val accessFault= Bool()
        val perm = UInt(3.W)
        val tlbContigousPerm = Bool()//仅对非H 拓展l0有效
        val permIsNAPOT = Bool()
        val source= UInt(mptSourceWidth.W)
        val mptLevel = UInt(log2Up(mptLevelLenOH).W)
        val mptOnly = Bool()
        val reqPA= UInt(ppnLen.W)
    })

    val respMiss = DecoupledIO(new Bundle {
        val hitLevel=UInt((mptLevelLenOH).W)
        val ppn = UInt(ppnLen.W)//minsize is 4k,dont need 12bits offset
        val source= UInt(mptSourceWidth.W)
        val PA= UInt((ppnLen).W)
        val mptOnly = Bool()
    })
    
   val refill = Flipped(ValidIO(new refillBundle()))
    
}

class MPTCache (implicit p: Parameters) extends XSModule with MPTCacheParam {
    val io = IO(new MPTCacheIO)
    ////mfence signal
    val mfenceActive = WireInit(false.B)
    val fencePA= WireInit(false.B)
    val mfencevalid= io.sfence.valid && io.sfence.bits.mfence.get
    //本mpt设计支持按pa刷新cache中的部分，刷新时除了叶节点外，同时也会把中间节点一并刷了(或许不用)
    switch(Cat(io.sfence.bits.rs2, io.sfence.bits.rs1).asUInt){ 
        is("b11".U) {
            fencePA:= (io.sfence.bits.id===io.csr.mmpt.sdid) && mfencevalid// 大概10层gate 延迟,无所谓
        }
        is("b01".U){
            fencePA:= mfencevalid
        }
        is("b10".U){
            mfenceActive:= (io.sfence.bits.id===io.csr.mmpt.sdid) && mfencevalid
        }
        is("b00".U){
            mfenceActive:= mfencevalid
        }
    }
    val flushAll = mfenceActive || io.csr.mmpt.changed
    val mptFlushReset = (reset.asBool || flushAll).asBool//当csr 变化或mfence，flush
    withReset (mptFlushReset){// 根据fence 信号把它全给刷了
        val pipeFlowEn= Wire(Bool())
        pipeFlowEn:= io.respMiss.ready & (! io.refill.valid)
        // 根据是否mfence-PA 是否refill 切换 pipeline input
        val PAfenceInputs = Wire(new MPTPipe)
        PAfenceInputs.reqPA :=  io.sfence.bits.addr
        PAfenceInputs.source := 0.U 
        PAfenceInputs.dataValid := false.B   
        PAfenceInputs.flushCache := true.B
        PAfenceInputs.mptOnly := DontCare   

        val ioInputs= Wire(new MPTPipe)
        ioInputs.reqPA := io.req.bits.reqPA
        ioInputs.source := io.req.bits.source        
        ioInputs.dataValid := io.req.fire
        ioInputs.flushCache := false.B
        ioInputs.mptOnly:= io.req.bits.mptOnly

        val refilling = Wire(Bool())
        val pipeInputs = Wire(new MPTPipe)
        val stageReq = Pipe(pipeFlowEn,pipeInputs,1)  
        val stageDelay= Pipe(pipeFlowEn, stageReq.bits,1)
        val stageCheck= Pipe(pipeFlowEn, stageDelay.bits,1)
        val stageResp= Pipe(pipeFlowEn, stageCheck.bits,1)
        pipeInputs := Mux(fencePA, PAfenceInputs, Mux(refilling,stageResp.bits,ioInputs))

        val ready = RegInit(true.B)
        io.req.ready := io.respMiss.ready && !fencePA && !refilling //blocking
        //init cache tag
        val l3Tag = Reg(Vec(l3Size, new mptCacheTag(tagLen = mptL3TagLen)))
        val l2Tag = Reg(Vec(l2Size, new mptCacheTag(tagLen = mptL2TagLen)))
        val l1Tag = Reg(Vec(l1Size,  new mptCacheTag(tagLen = mptL1TagLen))) 
 
        val spTag = Reg(Vec(spSize, new mptCacheTag(tagLen = mptspTagLen,isSp = true)))

        val l3Data = Reg(Vec(l3Size, new mptCacheData()))
        val l2Data = Reg(Vec(l2Size, new mptCacheData()))
        val l1Data = Reg(Vec(l1Size,  new mptCacheData())) 
        val spData = Reg(Vec(spSize, new mptCacheData(isPerms = true)))  
        val l0Data = Module(new SRAMTemplateMPT(new mptCacheL0(),set =  l0nSets, way = l0nWays))//1clk delay from req to resp
        val l0Valid = Reg(Vec(l0nSets,Vec(l0nWays, Bool())))

        val mptCacheL3Replace = Module(new PLRUOH(log_ways = log2Up(l3Size))).io
        val mptCacheL2Replace = Module(new PLRUOH(log_ways = log2Up(l2Size))).io
        val mptCacheL1Replace = Module(new PLRUOH(log_ways = log2Up(l1Size))).io
        val mptCacheL0Replace = Module(new PLRUOHSet(sets_log2 = log2Up(l0nSets),log_ways = log2Up(l0nWays))).io
        val mptCacheSpReplace = Module(new PLRUOH(log_ways = log2Up(spSize))).io
        //alloc replacement policy,use PLRU with Onehot in/out

        val (l3hit,l3hitPPN) ={
            val hitVecTemp = l3Tag.map{case(x) =>x.hit(stageReq.bits.reqPA) && x.valid}//hit when valid and tag equal stagereq
            when(stageReq.bits.flushCache)  {  // 一轮清空fence valid
                hitVecTemp.zipWithIndex.map{case(x,i)=> 
                    when(x){l3Tag(i).valid := false.B}
                }
            }
            val hitVec = RegEnable(VecInit(hitVecTemp), stageReq.bits.dataValid) //ready at stage check，使用datavalid 而不是 stageReq.valid ，这样内部逻辑在pipe内项无效时就不会切换了，省点电
            //val hitData= ParallelPriorityMux(hitVec zip l3Data)
            val hitData= RegEnable(Mux1H(hitVecTemp,l3Data), stageReq.bits.dataValid)//we can use onehot mux, should be faster.
            val hit=RegEnable(hitVecTemp.reduce(_||_), stageReq.bits.dataValid)// 1 bit hit ,avaliable at stage delay after 2 or gates
            
            mptCacheL3Replace.access.bits:= hitVec.asUInt //assign hitVec to plru to update plru state ,miss(hitVec = h0) will not change the plru state 
            mptCacheL3Replace.access.valid:=  stageDelay.bits.dataValid //ready at stage check
            (hit,hitData)
            
        }

        val (l2hit,l2hitPPN) ={
            val hitVecTemp = l2Tag.map{case(x) =>x.hit(stageReq.bits.reqPA) && x.valid}//hit when valid and tag equal stagereq
            when(stageReq.bits.flushCache)  {  // 一轮清空fence valid
                hitVecTemp.zipWithIndex.map{case(x,i)=> 
                    when(x){l2Tag(i).valid := false.B}
                }
            }
            val hitVec = RegEnable(VecInit(hitVecTemp), stageReq.bits.dataValid) //ready at stage check
            //val hitData= ParallelPriorityMux(hitVec zip l3Data)
            val hitData= RegEnable(Mux1H(hitVecTemp,l2Data), stageReq.bits.dataValid)//we can use onehot mux, should be faster.
            val hit=RegEnable(hitVecTemp.reduce(_||_), stageReq.bits.dataValid)// 1 bit hit ,avaliable at stage delay after 2 or gates
            
            mptCacheL2Replace.access.bits:= hitVec.asUInt //assign hitVec to plru to update plru state ,miss(hitVec = h0) will not change the plru state 
            mptCacheL2Replace.access.valid:=  stageDelay.bits.dataValid //ready at stage check
            (hit,hitData)
        }

        val (l1hit, l1hitPPN) ={
            val hitVecTemp = l1Tag.map{case(x) =>x.hit(stageReq.bits.reqPA) && x.valid}//hit when valid and tag equal stagereq
            when(stageReq.bits.flushCache)  {  // 一轮清空fence valid
                hitVecTemp.zipWithIndex.map{case(x,i)=> 
                    when(x){l1Tag(i).valid := false.B}
                }
            }            
            val hitVec = RegEnable(VecInit(hitVecTemp), stageReq.bits.dataValid) //ready at stage check
            //val hitData= ParallelPriorityMux(hitVec zip l3Data)
            val hitData= RegEnable(Mux1H(hitVecTemp,l1Data), stageReq.bits.dataValid)//we can use onehot mux, should be faster.
            val hit=RegEnable(hitVecTemp.reduce(_||_), stageReq.bits.dataValid)// 1 bit hit ,avaliable at stage delay after 2 or gates
            
            mptCacheL1Replace.access.bits:= hitVec.asUInt //assign hitVec to plru to update plru state ,miss(hitVec = h0) will not change the plru state 
            mptCacheL1Replace.access.valid:=  stageDelay.bits.dataValid //ready at stage check        
            (hit,hitData)

        }
        /////////////////////////// gen addr hit(l3-l1) at stage check
        //val(hitAddrLevelTemp,hitAddrT)=PriorityMux(Seq(l1hit,l2hit,l3hit),Seq(("b001".U,l1hitPPN),("b010".U, l2hitPPN),("b100".U,l3hitPPN))) 官方的PriorityMux 会在Select none 给出h0，但我要其它的default value
        val missLevel = Mux(io.csr.mmpt.mode === 2.U,"b1000".U,"b0100".U)//enablesmmpt52 = true, 0 delay since io.csr.mmpt.mode will not change during cache read
        val hitAddrLevelTemp= Mux(l1hit,"b0001".U,Mux(l2hit,"b0010".U,Mux(l3hit,"b0100".U,missLevel)))
        val hitAddrDataTemp= Mux(l1hit,l1hitPPN.data,Mux(l2hit,l2hitPPN.data,Mux(l3hit,l3hitPPN.data,io.csr.mmpt.ppn(ppnLen-1,0))))
        val hitAddrData= RegEnable(hitAddrDataTemp,stageDelay.bits.dataValid) 
        val hitAddrLevel=RegEnable(hitAddrLevelTemp,stageDelay.bits.dataValid)
        
        /////////////////////////// 
    
        val (l0hit, l0HitPerms,l0PermTlbCompress,l0PermIs64kNAPOT) ={
            val idx = getl0set(pipeInputs.reqPA) //..    
            
            l0Data.io.r.req.bits.apply(setIdx = idx)//.. 0 delay 相当于和stagereq的reg同时收到valid请求
            l0Data.io.r.req.valid:= pipeInputs.dataValid|| pipeInputs.flushCache//read and write at the same time will not cause error, but read is invalid 

            val l0validReg =  RegEnable(l0Valid(getl0set(stageReq.bits.reqPA)), stageReq.bits.dataValid|| stageReq.bits.flushCache)
            val dataResp = RegEnable(l0Data.io.r.resp.data, stageReq.bits.dataValid|| stageReq.bits.flushCache)//data avaliable at stage delay
            val setTag = dataResp.map(_.tag)
            val setData = dataResp.map(_.cacheData)//4 entry+tag
            //some wire
            val hitVecTemp = setTag.zip(l0validReg).map{case(x,v)=>x.hit(stageDelay.bits.reqPA) && v}//hit when valid and tag equal
            
            //delay (29 bit===):(1xnor + 5*and), (&& valid):(1 and) total 7
            //MfencePA
            when(stageDelay.bits.flushCache)  {  // 一轮清空fence valid
                hitVecTemp.zipWithIndex.map{case(x,i)=> 
                    when(x){l0Valid(getl0set(stageDelay.bits.reqPA))(i) := false.B}
                }
            }

            //
            val hitVec = RegEnable(VecInit(hitVecTemp),stageDelay.bits.dataValid)//valid at stage check
            val hitData= Mux1H(hitVecTemp,setData)//we use onehot mux, should be faster than ParallelPriorityMux. delay:log2(4)*2=4
            val hitDataReg= RegEnable(hitData,stageDelay.bits.dataValid)//valid at stage check, total delay 11 gates
            val hit=RegEnable(hitVecTemp.reduce(_||_),stageDelay.bits.dataValid)// 4-> 1 bit hit 

            val hitPermsTemp= hitDataReg.extractPerm(stageCheck.bits.reqPA(15,12))//always 15:12 delay log2(16)*3=12 gates

            mptCacheL0Replace.access.bits:= hitVec.asUInt //assign hitVec to plru to update plru state ,miss(hitVec = h0) will not change the plru state 
            mptCacheL0Replace.access.valid:=  stageCheck.bits.dataValid // processing at stage check, ready at stage resp
            mptCacheL0Replace.idx:= getl0set(stageCheck.bits.reqPA)

            val PermsAsVec = Wire(Vec(16,UInt(3.W))) //perm xwr bits, total 16 xwrs in one mpte
            for (i <- 0 until 16) {PermsAsVec(i):= hitDataReg.data((2+ i*3), (i*3))}
            val PermsEqual = Wire(Vec(16-1,Bool()))
            for (i <- 0 until 16-1) {PermsEqual(i):= PermsAsVec(i+1) === PermsAsVec(i)}//delay 1XNOR + 2 and gates = 3   
            val low8PermsAllEqual = PermsEqual.slice(0,7).reduce(_&&_) //=PermsEqual(6,0), delay 3
            val high8PermsAllEqual = PermsEqual.slice(8,15).reduce(_&&_) //=PermsEqual(14,8)
            val allEqual = low8PermsAllEqual && high8PermsAllEqual && PermsEqual(7) //Delay 2
            val tlbCompress= Mux( stageCheck.bits.reqPA(15,12) < 8.U,low8PermsAllEqual, high8PermsAllEqual)//delay 3
            
            (hit,RegEnable(hitPermsTemp,stageCheck.bits.dataValid),RegEnable(tlbCompress,stageCheck.bits.dataValid),RegEnable(allEqual,stageCheck.bits.dataValid))//ready at stage resp,hit reaady at stage check
        }
    
        val (sPhit,spHitPerms,spPermIsNAPOT,splevel) = {
            val hitVecTemp = spTag.map(x=>x.hitSp(stageReq.bits.reqPA) && x.valid)//hit when valid and tag equal delay 7 + mux1h delay 4 gates
            when(stageReq.bits.flushCache)  {  // 一轮清空fence valid
                hitVecTemp.zipWithIndex.map{case(x,i)=> 
                    when(x){spTag(i).valid := false.B}
                }
            }

            val hitVec = RegEnable(VecInit(hitVecTemp), stageReq.bits.dataValid) //ready at stage delay
            ////////
            val levelVec = spTag.map(x=>x.level.get)
            val level = Mux1H(hitVec,levelVec)//ready at stage delay, require cache to be consistent
            val levelReg= RegEnable(level,stageDelay.bits.dataValid)   
            val levelUInt = Wire(UInt(mptLevelLenUInt.W))//4levels len 2 
            levelUInt:= OHToUInt(Cat(levelReg,0.U(1.W)))   

            val extractOffset= Mux1H( level, Seq(
            stageDelay.bits.reqPA(15+9*3,12+9*3),
            stageDelay.bits.reqPA(15+9*2,12+9*2),
            stageDelay.bits.reqPA(15+9,12+9)
            ))

            val extractOffsetReg= RegEnable(extractOffset,stageDelay.bits.dataValid) //ready at stage check

            //val hitData= ParallelPriorityMux(hitVec zip l3Data)
            val hitData = Mux1H(hitVec,spData)//we can use onehot mux, should be faster.
            val hitDataReg = RegEnable(hitData,stageDelay.bits.dataValid)//valid at stage check, total delay 11 gates
            val hitPermsTemp = hitDataReg.extractPerm(extractOffsetReg)//always 15:12 delay log2(16)*3=12 gates
            val hit=RegEnable(hitVec.reduce(_||_), stageDelay.bits.dataValid)// 1 bit hit 
            
            mptCacheSpReplace.access.bits:= hitVec.asUInt //assign hitVec to plru to update plru state ,miss(hitVec = h0) will not change the plru state 
            mptCacheSpReplace.access.valid:=  stageDelay.bits.dataValid //ready at stage check
            
            val PermsAsVec = Wire(Vec(16,UInt(3.W))) //perm xwr bits, total 16 xwrs in one mpte
            for (i <- 0 until 16) {PermsAsVec(i):= hitDataReg.data((2+ i*3), (i*3))}
            val PermsEqual = Wire(Vec(16-1,Bool()))
            for (i <- 0 until 16-1) {PermsEqual(i):= PermsAsVec(i+1) === PermsAsVec(i)}//delay 1XNOR + 2 and gates = 3   
            val allEqual = PermsEqual.reduce(_&&_) //=PermsEqual, delay 4

            (hit,RegEnable(hitPermsTemp,stageCheck.bits.dataValid),RegEnable(allEqual,stageCheck.bits.dataValid),RegEnable(levelUInt,stageCheck.bits.dataValid))//ready at stage resp,hit reaady at stage check
        }
    ///////gen perms hit l0 sp at stage check 

        val hitPerms = sPhit || l0hit
        io.respHit.valid := RegEnable(hitPerms & stageCheck.bits.dataValid,stageCheck.valid)//无论是否datavalid都读入，data invalid 则hit也invalid，此时的hitperms实为上一个pipe的结果
        val (sPhitReg,l0hitReg) = (RegEnable(sPhit,stageCheck.bits.dataValid),RegEnable(l0hit,stageCheck.bits.dataValid))
        io.respHit.bits.perm := Mux1H(Seq(sPhitReg,l0hitReg),Seq(spHitPerms,l0HitPerms)) //1 mux at output, 2 gates, should be fine
        io.respHit.bits.source := stageResp.bits.source //转一圈回去
        io.respHit.bits.mptOnly:= stageResp.bits.mptOnly
        io.respHit.bits.reqPA:= stageResp.bits.reqPA(PAddrBits-1,offLen)
        io.respHit.bits.tlbContigousPerm:= l0PermTlbCompress
        io.respHit.bits.permIsNAPOT:=  Mux1H(Seq(sPhitReg,l0hitReg),Seq(spPermIsNAPOT,l0PermIs64kNAPOT)) 
        io.respHit.bits.accessFault:=false.B//entry in mpt cache is always valid 
        io.respHit.bits.mptLevel:= Mux1H(Seq(sPhitReg,l0hitReg),Seq(splevel,0.U(mptLevelLenUInt.W)))//splevel is converted to binary for l1/l2tlb level compare with s1pte and s2pte


        io.respMiss.valid := RegEnable(!hitPerms &  stageCheck.bits.dataValid,stageCheck.valid)//无论是否datavalid都读入
        io.respMiss.bits.hitLevel := RegEnable(hitAddrLevel,stageCheck.bits.dataValid)
        io.respMiss.bits.ppn := RegEnable(hitAddrData,stageCheck.bits.dataValid)
        io.respMiss.bits.source := stageResp.bits.source
        io.respMiss.bits.mptOnly:= stageResp.bits.mptOnly
        io.respMiss.bits.PA:= stageResp.bits.reqPA(PAddrBits-1,offLen)
        ////read logic end
        ////refill write logic start
        //如果使用循环pipe 解决refill冲突问题，循环时cache 会被同样的tag 访问两次，对TLRU来说，不是问题,LRU队列不变，但对于PLRU来说呢？应该也问题不大？
        val refillCounter= RegInit("b0000".U)

        when(io.refill.valid) {
            refillCounter:="b1000".U
        } .otherwise{
            refillCounter:=refillCounter>>1
        }

        // when(io.refill.valid) {pipeFlowEn:= false.B } 移至开头初始化部分
        refilling:= refillCounter.orR// is refiill state when counter != 0 做4回合接头霸王



 

        ///////////////////若如果使用TLRU，如果cache为空，lru指向的也应该是空节点，因为空节点根本没被访问过，因此可以照常使用lru指向的节点refill
        //若如果使用PLRU，如果cache为空，访问空节点的临近节点会导致该空节点不被lru所指向 例如 若使用 长度4 PLRU 序列ABACAD 会导致B被D覆盖，而A边上的空节点不会被写入
        //可以在cache 不满的时候先从上到下填满，不管plru
        //但是，由于时序紧张，先试试只用plru，看看有多少浪费
        val l3RefillEn = io.refill.bits.level(3).asBool & (!io.refill.bits.isLeafMpte) & io.refill.valid
        val rfl3Tag = io.refill.bits.PA(PAddrBits- MptOff-1, PAddrBits- MptOff- mptL3TagLen)
        val l3VictimWay = mptCacheL3Replace.replace// ready after idx is set , OH encoding

        val l2RefillEn = io.refill.bits.level(2).asBool & (!io.refill.bits.isLeafMpte)& io.refill.valid
        val rfl2Tag = io.refill.bits.PA(PAddrBits- MptOff-1, PAddrBits- MptOff- mptL2TagLen)
        val l2VictimWay = mptCacheL2Replace.replace// ready after idx is set , OH encoding

        val l1RefillEn = io.refill.bits.level(1).asBool & (!io.refill.bits.isLeafMpte)& io.refill.valid
        val rfl1Tag = io.refill.bits.PA(PAddrBits- MptOff-1, PAddrBits- MptOff- mptL1TagLen)
        val l1VictimWay = mptCacheL1Replace.replace// ready after idx is set , OH encoding

        val l0RefillEn = io.refill.bits.level(0).asBool & (io.refill.bits.isLeafMpte) &  io.refill.valid
        val rfl0Tag = io.refill.bits.PA(PAddrBits- MptOff-1, PAddrBits- MptOff- mptL0TagLen)
        val rfl0SetIdx = io.refill.bits.PA(PAddrBits- MptOff- mptL0TagLen-1, 0)
        val l0VictimWay = mptCacheL0Replace.replace// ready after idx is set , OH encoding


        val spRefillEn = (!io.refill.bits.level(0).asBool) & io.refill.bits.isLeafMpte & io.refill.valid
        val rfspTag = io.refill.bits.PA(PAddrBits- MptOff-1, PAddrBits- MptOff- mptspTagLen)
        val spVictimWay = mptCacheSpReplace.replace // 

        ///write data into cache 1 cycle 
        val l0Wdata = Wire(new mptCacheL0()) // 0 delay ,wire signal assignment
        l0Wdata.tag.tag := rfl0Tag
        l0Wdata.tag.valid := true.B
        l0Wdata.cacheData.data := io.refill.bits.refillData.data // 等有空把class 的子类父类重写一遍
        l0Data.io.w.req <> DontCare //default val for write channel is invalid 
        l0Data.io.w.req.valid := false.B
        when (l0RefillEn) {
            l0Data.io.w.apply(
            valid = true.B, //valid when refill
            setIdx = rfl0SetIdx,
            data = l0Wdata,
            waymask = l0VictimWay
            )
            mptCacheL0Replace.idx:= rfl0SetIdx //覆盖pipeline的赋值，这里不太明显，或许可以把信号单独拎出来
            //refill时切换plru输入至refill数据并立即更新，4way更新延迟：2 gates，32组idx切换3 gates，l0 refillEn 1 gates,mux refillEn切换输入 3 gates
            mptCacheL0Replace.access.bits:= l0VictimWay
            mptCacheL0Replace.access.valid:= true.B
        }

        when (l3RefillEn) {
            for (i <- 0 until l3Size) {
                when(l3VictimWay(i)===1.U){
                    l3Tag(i).tag := rfl3Tag 
                    l3Tag(i).valid := true.B
                    l3Data(i).data:= io.refill.bits.refillData.getPPN 
                }
            }
            mptCacheL3Replace.access.bits:= l3VictimWay
            mptCacheL3Replace.access.valid:= true.B
        }

        when (l2RefillEn) {
            for (i <- 0 until l2Size) {
                when(l2VictimWay(i)===1.U){
                    l2Tag(i).tag := rfl2Tag 
                    l2Tag(i).valid := true.B
                    l2Data(i).data:= io.refill.bits.refillData.getPPN 
                }
            }
            mptCacheL2Replace.access.bits:= l2VictimWay
            mptCacheL2Replace.access.valid:= true.B
        }
        when (l1RefillEn) {
             for (i <- 0 until l1Size) {
                when(l1VictimWay(i)===1.U){
                    l1Tag(i).tag := rfl1Tag 
                    l1Tag(i).valid := true.B
                    l1Data(i).data:= io.refill.bits.refillData.getPPN 
                }
            }
            mptCacheL1Replace.access.bits:= l1VictimWay
            mptCacheL1Replace.access.valid:= true.B
        }
        when (spRefillEn) {
            /*spVictimWay.zipWithIndex.map{case(en,i) => // update cache content
                when(en){*/
            for (i <- 0 until spSize) {
                when(spVictimWay(i)===1.U){    
                    spTag(i).tag    := rfspTag 
                    spTag(i).valid  := true.B
                    spTag(i).level.get  := io.refill.bits.level(3,1)
                    spData(i).data  := io.refill.bits.refillData.data 
                }
            }
            mptCacheSpReplace.access.bits:= spVictimWay
            mptCacheSpReplace.access.valid:= true.B
        }
    }
}
////////////////////////////////////////// MSHR START ///////////////////////////////////////////////////////////////////////////////
class MSHRreg()(implicit p: Parameters) extends XSBundle with MPTCacheParam {
    val hitAddr =  UInt(ppnLen.W) 
    val level = UInt((mptLevelLenOH).W)
    val reqPA= UInt((PAddrBits- MptOff).W)
    val valid = Bool()
}

class permTable() (implicit p: Parameters) extends XSBundle with MPTCacheParam {
    val source = UInt(mptSourceWidth.W)
    val offset= UInt((MptOff-12).W) //offset to decide which perm to use
    val tag =UInt(1.W)
    val mptOnly = Bool()
    //val valid=Bool() we are using a queue valid is not needed
}

class mshrToTWReqBundle(implicit p: Parameters) extends XSBundle with MPTCacheParam {
    val hitAddr =  UInt(ppnLen.W)
    val reqPA = UInt((PAddrBits- MptOff).W)
    val hitLevel = UInt(mptLevelLenOH.W)
}
class TWtomshrRespBundle(implicit p: Parameters) extends XSBundle with MPTCacheParam {
        val perms = new mptData()
        val mptTWLevel = UInt(mptLevelLenOH.W)
        //val reqPA = UInt((PAddrBits- MptOff).W)
        val AccessFault = Bool()
}
class MSHRIO(implicit p: Parameters) extends XSBundle with MPTCacheParam {
    val missCache =Flipped(DecoupledIO(new Bundle {
        val hitLevel=UInt((mptLevelLenOH).W)
        val hitAddr = UInt(ppnLen.W)//hit addr 
        val source= UInt(mptSourceWidth.W)
        val PA= UInt((ppnLen).W)//req pa minsize is 4k,dont need 12bits offset
        val mptOnly= Bool()//1bit control signal for tlb, does basically nothing in mptc
    }   ) )

    val twReq = DecoupledIO(new mshrToTWReqBundle())

    val twFin = Flipped(DecoupledIO(new TWtomshrRespBundle()))

    val resp = ValidIO(new Bundle {// source is waiting for cache to resp
        val AccessFault = Bool()
        val mptLevel = UInt(mptLevelLenOH.W)
        val perm = UInt(3.W)
        val PermTlbCompress = Bool()
        val permIsNAPOT = Bool()
        val mptOnly = Bool()
        val reqPA = UInt(ppnLen.W)
        val source= UInt(mptSourceWidth.W)
    })

}

class MSHR(implicit p: Parameters) extends XSModule with MPTCacheParam {
    val io=IO(new MSHRIO)

    val fsmIDLE = Wire(Bool()) //when busy stop read and send(can still send? maybe) 
    val sendTwEn =  Wire(Bool())

    val TWResp = RegEnable(io.twFin.bits,io.twFin.fire)//store the tw resp to reg

    val mshrRegInst= Reg(Vec(2, new MSHRreg()))   //MSHR reg records PA
    val mshrRegAddr = Reg(UInt(1.W)) //indicate the current FSM and wirte MSHR
    val sendActive= Wire(UInt(1.W))//

    val mshrRegFull = mshrRegInst.map(_.valid).reduce(_&&_)
    val mshrRegEmpty = !(mshrRegInst.map(_.valid).reduce(_||_))

    val permTableFIFO = Module(new Queue(new permTable() ,8)).io //FIFO queue,record offset

    val tableNotFull = permTableFIFO.enq.ready
    val tableNotEmpty = permTableFIFO.deq.valid
    io.missCache.ready := tableNotFull && !(mshrRegFull) && fsmIDLE //ready when both not full

    permTableFIFO.enq.valid := io.missCache.fire// 无论如何，fire时都要录入table
    permTableFIFO.enq.bits.source:= io.missCache.bits.source
    permTableFIFO.enq.bits.offset:= io.missCache.bits.PA(MptOff-offLen-1,0)//3-0 offset
    permTableFIFO.enq.bits.mptOnly:= io.missCache.bits.mptOnly
    permTableFIFO.enq.bits.tag:= mshrRegAddr
    when(io.missCache.fire & (mshrRegInst(mshrRegAddr).reqPA =/= io.missCache.bits.PA(ppnLen-1, MptOff-offLen))){//when 4k addr does not repeat
        mshrRegInst(mshrRegAddr+1.U).hitAddr := io.missCache.bits.hitAddr
        mshrRegInst(mshrRegAddr+1.U).level :=  io.missCache.bits.hitLevel
        mshrRegInst(mshrRegAddr+1.U).reqPA := io.missCache.bits.PA(ppnLen-1, MptOff-offLen)
        mshrRegInst(mshrRegAddr+1.U).valid :=  true.B
        permTableFIFO.enq.bits.tag:= mshrRegAddr+1.U
        when(mshrRegEmpty){//when empty,points to the newly written MSHR
            mshrRegAddr:= mshrRegAddr+1.U
             
        }
    } 
    //mshr write logic end, write to not mshrRegAddr mshr
    io.twReq.bits.hitAddr:=mshrRegInst(sendActive).hitAddr
    io.twReq.bits.reqPA:=mshrRegInst(sendActive).reqPA
    io.twReq.bits.hitLevel:=mshrRegInst(sendActive).level
    io.twReq.valid:= mshrRegInst(sendActive).valid && sendTwEn
    //mshr send end, send the mshr which has been pointed by mshrRegAddr to tw,repeat sending is not possible,since mshrRegAddr will change as soon as the twresp is recorded
    
    val retPermOffset= Mux1H(Seq(//different level use different offset 
        TWResp.mptTWLevel(3)-> mshrRegInst(mshrRegAddr).reqPA(9*3-1,9*3-4),
        TWResp.mptTWLevel(2)-> mshrRegInst(mshrRegAddr).reqPA(9*2-1,9*2-4),
        TWResp.mptTWLevel(1)-> mshrRegInst(mshrRegAddr).reqPA(9-1,9-4),
        TWResp.mptTWLevel(0)-> permTableFIFO.deq.bits.offset)) //read from table entry instead
    io.resp.bits.perm :=TWResp.perms.extractPerm(retPermOffset)// mshr return bits when AccessFault,return 000 not allow, else perm val 
    io.resp.bits.AccessFault := TWResp.AccessFault
    io.resp.bits.source := permTableFIFO.deq.bits.source
    io.resp.bits.mptOnly:= permTableFIFO.deq.bits.mptOnly
    
    val PermsAsVec = Wire(Vec(16,UInt(3.W))) //perm xwr bits, total 16 xwrs in one mpte
    for (i <- 0 until 16) {PermsAsVec(i):= TWResp.perms.data((2+ i*3), (i*3))}
    val PermsEqual = Wire(Vec(16-1,Bool()))
    for (i <- 0 until 16-1) {PermsEqual(i):= PermsAsVec(i+1) === PermsAsVec(i)}//delay 1XNOR + 2 and gates = 3   
    val leftPermsAllEqual = PermsEqual.slice(0,7).reduce(_&&_) //=PermsEqual(6,0), delay 3
    val rightPermsAllEqual = PermsEqual.slice(8,15).reduce(_&&_) //=PermsEqual(14,8)
    io.resp.bits.permIsNAPOT := leftPermsAllEqual && rightPermsAllEqual && PermsEqual(7) //Delay 2
    io.resp.bits.PermTlbCompress := Mux(permTableFIFO.deq.bits.offset<8.U,leftPermsAllEqual, rightPermsAllEqual)//delay 3

    io.resp.bits.mptLevel:= OHToUInt(TWResp.mptTWLevel) //convert to UInt
    io.resp.bits.reqPA := Cat(mshrRegInst(mshrRegAddr).reqPA , permTableFIFO.deq.bits.offset)//return reqPa is MSHR tag + offset 
    val mshrRetAllL3 = mshrRegInst(0).reqPA(PAddrBits- MptOff - 1,PAddrBits- MptOff-mptL3TagLen) === mshrRegInst(1).reqPA(PAddrBits- MptOff - 1,PAddrBits- MptOff-mptL3TagLen)&&mshrRegFull
    //大页两种情况会继续return 1. mshr0/1 地址同属一个大页地址空间 mshrRetAllLn===true.B 并且都valid2 当前table项属于当前active mshr 
    val mshrRetAllL2 = mshrRegInst(0).reqPA(PAddrBits- MptOff - 1,PAddrBits- MptOff-mptL2TagLen) === mshrRegInst(1).reqPA(PAddrBits- MptOff - 1,PAddrBits- MptOff-mptL2TagLen)&&mshrRegFull
    val mshrRetAllL1 = mshrRegInst(0).reqPA(PAddrBits- MptOff - 1,PAddrBits- MptOff-mptL1TagLen) === mshrRegInst(1).reqPA(PAddrBits- MptOff - 1,PAddrBits- MptOff-mptL1TagLen)&&mshrRegFull
    val mshrAllowRetAll= Mux1H(Seq(
        TWResp.mptTWLevel(3)-> mshrRetAllL3,
        TWResp.mptTWLevel(2)-> mshrRetAllL2,
        TWResp.mptTWLevel(1)-> mshrRetAllL1,
        TWResp.mptTWLevel(0)-> false.B//4k addr len can not repeat
    )) //delay TODO***

    // mshr return valid using FSM(or maybe not,since it only has two states)

    object mshrstate extends ChiselEnum {
            val sIDLE , sProc = Value
        }
    import mshrstate._ 
    val curState = RegInit(sIDLE)
    val nextState = WireDefault(sIDLE)
    curState:= nextState// 2 proc FSM 

    nextState := curState
    io.twFin.ready := false.B
    fsmIDLE:= false.B
    permTableFIFO.deq.ready:= false.B
    io.resp.valid:= false.B
    sendActive:= mshrRegAddr
    sendTwEn :=  false.B 
    switch(curState) {
        is(sIDLE) {
            io.twFin.ready := true.B//can receive tw resp
            fsmIDLE:= true.B//can receive cache request 
            sendTwEn:= true.B
            when(io.twFin.fire){
                nextState:= sProc
                //fsmIDLE:= false.B//disable cache req input
            }   
        }
        is(sProc) {
            when (! mshrAllowRetAll){ 
                sendTwEn:= true.B 
                sendActive := mshrRegAddr+1.U
            }//if valid, send tw the req without waiting the return perm to finish. only possible when not mshrAllowRetAll,大概快4clk吧，聊胜于无
            when (permTableFIFO.deq.valid && (mshrAllowRetAll || mshrRegAddr === permTableFIFO.deq.bits.tag)){//there is something in the queue
                //大页两种情况会继续return 1. mshr0/1 地址同属一个大页地址空间 mshrRetAllLn===true.B 并且都valid2 当前table项属于当前active mshr          
                permTableFIFO.deq.ready:= true.B //pop queue until empty
                io.resp.valid:= true.B
            } .otherwise{
                nextState:= sIDLE
                mshrRegAddr:= mshrRegAddr+1.U
                when (mshrAllowRetAll) {
                    mshrRegInst(0).valid:=false.B
                    mshrRegInst(1).valid:=false.B
                }.otherwise{
                    mshrRegInst(mshrRegAddr).valid:=false.B
                }
            }
        }
    }
}


class mptTableWalkerIO(implicit p: Parameters) extends MMUIOBaseBundle with HasPtwConst {
    val req = Flipped(DecoupledIO(new mshrToTWReqBundle()))
    
    val resp = DecoupledIO(new TWtomshrRespBundle())

    val mem = new Bundle {
        val req = DecoupledIO(new Bundle { val addr = UInt(PAddrBits.W)})
        val resp = Flipped(ValidIO(UInt(XLEN.W)))//改片选
        //val mask = Input(Bool()) dont need？ 
    }

    val pmp = new Bundle {//是否用pmp
        val req = ValidIO(new PMPReqBundle())
        val resp = Flipped(new PMPRespBundle())
    }
    val refill = ValidIO(new refillBundle()) 

}

 
class MPTTableWalker (implicit p: Parameters) extends XSModule with MPTCacheParam{
    val io=IO(new mptTableWalkerIO)
    val mem=io.mem 
    
    io.pmp.req.bits.size := 3.U//不知道是什么，反正ptw这样做
    io.pmp.req.bits.cmd := TlbCmd.read

    val flush=io.sfence.valid || io.csr.mmpt.changed
    val mptFlushReset= (reset.asBool || flush).asBool//当csr 变化或mfence，flush
    withReset (mptFlushReset){//
        ////////////////
        val pa = RegEnable(io.req.bits.reqPA, 0.U,io.req.fire)//收到的req pa,存入 reg, 用来生成pn123 offset 合成表地址
        io.refill.bits.PA := pa
        ////////////////////////////////////////////////////////////////////
        val mpteResp =Wire(new mptEntry())
        mpteResp.apply(mem.resp.bits)// mem 返回的转化mpte，存入 mpteData
        // 定义level寄存器
        val setLevel= Wire(Bool())
        val setPmpCheckLevel= Wire(Bool())
        val nextLevel = Wire(UInt(mptLevelLenOH.W))
        val nextPmpCheckLevel = Wire(UInt(mptLevelLenOH.W))

        val level = RegEnable(nextLevel,"b1000".U(mptLevelLenOH.W),setLevel)
        val pmpCheckLevel = RegEnable(nextPmpCheckLevel,"b1000".U(mptLevelLenOH.W),setPmpCheckLevel)

 


        //////

        val mpteData = Reg(new mptData())//存返回的perm/下级addr 或者 发送来的req addr enter， 用来返回perms 或者 与pa 合成下级页表
        io.resp.bits.perms:= mpteData// output alloc
        io.refill.bits.refillData:= mpteData// output alloc
        val isLeafMpte=RegEnable(mpteResp.isLeaf,false.B,io.mem.resp.valid)
        io.refill.bits.isLeafMpte := isLeafMpte// tell cache if the current refill is leaf node 
        val mpteInvalid=RegEnable(!mpteResp.isValid,false.B,io.mem.resp.valid)//1 level not on top of mem.resp 
        val rsvZeroError0=RegEnable(mem.resp.bits(9,2).orR,false.B,io.mem.resp.valid)//max 3 level or gate on top of mem.resp，NON ZERO error of mtpe
        //val rsvZeroError1=RegEnable(mem.resp.bits(62)===1.U ,false.B,io.mem.resp.valid)
        //val rsvZeroError2=RegEnable(( mpteResp.isLeaf && mem.resp.bits(61:58).orR),false.B,io.mem.resp.valid)
        val rsvZeroError1=RegEnable(mem.resp.bits(62,58).orR,false.B,io.mem.resp.valid)// 地址仅48位，高位为0，中间节点一样可以用同样的范围查zero
        val rsvZeroError2=false.B
        when(io.req.fire) {
            mpteData.apply(io.req.bits.hitAddr)
        }.elsewhen(io.mem.resp.valid){
            mpteData:=mpteResp.data
        }

        val pn=Wire(UInt(9.W)) //用level 和 pa 生成pn
        pn:=(Fill (9,level(3)) & Cat(0.U(4.W),pa(47-MptOff,43-MptOff))) | (Fill (9,level(2)) & pa(42-MptOff,34-MptOff)) | (Fill (9,level(1)) & pa(33-MptOff,25-MptOff)) | (Fill (9,level(0)) & pa(24-MptOff,16-MptOff))

        //pn:=Mux1H(Seq())

        //3 layers of gate logic select the coresponding PN[i] based on cur level,just a onehot mux 
        val memAddr = mpteData.getAddr(pn)//生成访问的addr， cat wire 0 延迟
        io.mem.req.bits.addr:= memAddr
        //////////////////////////////////////////////////////////////// PMP 可能的时序问题， mem 返回值直接PMP check?事先预防，先打一拍
        io.pmp.req.valid:= DontCare 
        io.pmp.req.bits.addr:= Mux(io.mem.resp.valid, mpteResp.getAddr(pn), memAddr)//should be safer than just := memAddr
        //io.pmp.req.bits.cmd := TlbCmd.read // uncomment 
        //io.pmp.req.bits.size := 3.U // TODO: fix it
        ////AccessFault logic
        val pmpFail= (!isLeafMpte)&&(io.pmp.resp.ld || io.pmp.resp.mmio) //PMP delay unknown 
        val entryError= mpteInvalid|| rsvZeroError0|| rsvZeroError1 || rsvZeroError2 ||((!isLeafMpte) && level===0.U)//level==0 non leaf, zero=/=0,pmp fail,invalid casue AccessFault
        val AccessFault= entryError|| pmpFail//pmp fail also cause AccessFault
       
        io.resp.bits.mptTWLevel:= Mux(pmpFail,pmpCheckLevel,level)//pmpFail return next level,else cur level
        io.resp.bits.AccessFault:= AccessFault    

        io.refill.bits.level:= level
        // pmp fail will not be recorded(if the root addr+ pn[i] cause pmp fail does not necessarily mean that the root addr + other offset will cause pmp fail, so entry will be refilled as a normal intermidiate node)
        //////////////////////////////FSM

    object mystate extends ChiselEnum {
            val sIDLE , sMEM_REQ, sMEM_RESP, sADDR_PROC, sMSHR_RETURN = Value
        }
    import mystate._
    
        //val sIDLE :: sMEM_REQ :: sMEM_RESP :: sADDR_PROC :: sMSHR_RETURN  :: Nil = Enum(5)
        val curState = RegInit(sIDLE)
        val nextState = WireDefault(sIDLE)
        curState:= nextState// 2 proc FSM 
        //fsm start
            mem.req.valid := false.B
            io.req.ready:= false.B
            nextState := curState
            setLevel:= false.B
            setPmpCheckLevel:=false.B
            nextLevel:=level>> 1.U //onehotcounter-1 只用一个就行 不用aflevel***改!!! 
            nextPmpCheckLevel:=pmpCheckLevel>> 1.U
            io.refill.valid:= false.B
            io.resp.valid:= false.B
        //default val
            switch(curState) {
                is(sIDLE) {
                    io.req.ready:= true.B
                    when(io.req.fire){//fire 不是信号，是 ready&valid 把它当信号用会出错
                        setPmpCheckLevel:=true.B
                        nextLevel:= io.req.bits.hitLevel
                        nextPmpCheckLevel:=io.req.bits.hitLevel
                        nextState := sMEM_REQ//to mem req if fire 
                    }
                }
                is(sMEM_REQ) {
                    mem.req.valid:= true.B//req valid when not fire                    
                  
                    when(io.mem.req.fire) {//just waiting, timing safe
                        nextState := sMEM_RESP //to wait resp
                    }.otherwise{
 
                    }
                }
                is(sMEM_RESP) {//unknown in delay,timing?
                    when(io.mem.resp.valid) {//do nothing,delay one cycle OPTPOINT*
                    nextState := sADDR_PROC
                    setPmpCheckLevel:= true.B
                    }
                }
                is(sADDR_PROC) {//known delay
                // 处理返回的节点
                    when(AccessFault||isLeafMpte){//out delay unknown 
                        nextState :=sMSHR_RETURN    //OPTPOINT*
                    }.otherwise{
                        io.refill.valid:= true.B//start refill
                        setLevel:=true.B
                        nextState :=sMEM_REQ    //OPTPOINT*
                    }      
                }
                is(sMSHR_RETURN) {
                    io.resp.valid:= true.B
                    when(io.resp.fire) {
                        nextState := sIDLE
                    }
                }
            }
        //fsm end

         
    }
}

class mptCheckerIO(implicit p: Parameters) extends MMUIOBaseBundle with HasPtwConst {
val mem = new Bundle {
    val req = DecoupledIO(new L2TlbMemReqBundle())
    val resp = Flipped(ValidIO(UInt(XLEN.W)))
    val mask = Input(Bool())//mask bit 
  }
    val req = Flipped(DecoupledIO(new mptReqBundle()))
    val resp = ValidIO(new mptRespBundle())

    val pmp = new Bundle {
        val req = ValidIO(new PMPReqBundle())
        val resp = Flipped(new PMPRespBundle())
    }
}

class mptChecker(implicit p: Parameters) extends XSModule with HasPtwConst {
    val io = IO(new mptCheckerIO)
    io.mem.req.bits.hptw_bypassed := true.B//never refill to page cache
    io.mem.req.bits.id:=mptcMemReqID.U(bMemID.W)
    val mptCacheInst    = Module((new MPTCache())).io
    val mptTWInst       = Module((new MPTTableWalker())).io
    val mshrInst        = Module((new MSHR())).io
 
    mptCacheInst.csr <> io.csr // 
    mptCacheInst.sfence <> io.sfence // 
    
    mptTWInst.csr <> io.csr // 
    mptTWInst.sfence  <> io.sfence  // 
    

    //cache请求输入mptcache
    mptCacheInst.req.bits.mptOnly:= io.req.bits.mptOnly//need some fix 
    mptCacheInst.req.bits.reqPA := io.req.bits.reqPA
    mptCacheInst.req.bits.source := io.req.bits.id
    mptCacheInst.req.valid:=  io.req.valid
    io.req.ready:= mptCacheInst.req.ready
    //cache hit/mshr结果返回，根据mshr valid 切换
 

    val mptReturn = Wire(new mptRespBundle())
    mptReturn.mptPerm := Mux(mshrInst.resp.valid, mshrInst.resp.bits.perm, mptCacheInst.respHit.bits.perm) 
    mptReturn.contigousPerm := Mux(mshrInst.resp.valid, mshrInst.resp.bits.PermTlbCompress, mptCacheInst.respHit.bits.tlbContigousPerm)
    mptReturn.id := Mux(mshrInst.resp.valid, mshrInst.resp.bits.source, mptCacheInst.respHit.bits.source)
    mptReturn.mptLevel:= Mux(mshrInst.resp.valid, mshrInst.resp.bits.mptLevel, mptCacheInst.respHit.bits.mptLevel)
    mptReturn.mptOnly:= Mux(mshrInst.resp.valid, mshrInst.resp.bits.mptOnly, mptCacheInst.respHit.bits.mptOnly)
    mptReturn.reqPA:= Mux(mshrInst.resp.valid, mshrInst.resp.bits.reqPA, mptCacheInst.respHit.bits.reqPA)
    mptReturn.accessFault:=  Mux(mshrInst.resp.valid, mshrInst.resp.bits.AccessFault, mptCacheInst.respHit.bits.accessFault)
    mptReturn.permIsNAPOT :=  Mux(mshrInst.resp.valid, mshrInst.resp.bits.permIsNAPOT, mptCacheInst.respHit.bits.permIsNAPOT)

    io.resp.valid := mshrInst.resp.valid||mptCacheInst.respHit.valid
    io.resp.bits <> mptReturn
    //cache miss 发送mshr
    mshrInst.missCache.bits.mptOnly:=  mptCacheInst.respMiss.bits.mptOnly
    mshrInst.missCache.bits.hitLevel:= mptCacheInst.respMiss.bits.hitLevel
    mshrInst.missCache.bits.hitAddr:= mptCacheInst.respMiss.bits.ppn
    mshrInst.missCache.bits.source:=  mptCacheInst.respMiss.bits.source
    mshrInst.missCache.bits.PA:= mptCacheInst.respMiss.bits.PA
    mshrInst.missCache.valid:= mptCacheInst.respMiss.valid
    mptCacheInst.respMiss.ready:= mshrInst.missCache.ready
    //cache refill 接口
    mptCacheInst.refill <> mptTWInst.refill
    // mshr-tw请求接口
    mptTWInst.req <> mshrInst.twReq
   // tw-mshr 返回接口
    mshrInst.twFin <>  mptTWInst.resp 
    //table walk 读取ram    
    io.mem.req.bits.addr:= mptTWInst.mem.req.bits.addr
    io.mem.req.valid := mptTWInst.mem.req.valid
    mptTWInst.mem.req.ready:= io.mem.req.ready

    mptTWInst.mem.resp.bits:= io.mem.resp.bits//改宽度
    mptTWInst.mem.resp.valid:= io.mem.resp.valid
    //mptTWInst.mem.resp.ready:= true.B   
    //PMP 接口
    mptTWInst.pmp.resp <> io.pmp.resp
    io.pmp.req<> mptTWInst.pmp.req 

    when (io.csr.mmpt.mode === 0.U){
        mptCacheInst.req.valid:= false.B //mptmode === bare 关闭mpt输入，还要在L2TLB中做一个mux，如果mpt关闭则返回权限111
    }
}

/* 未完成
无

*/