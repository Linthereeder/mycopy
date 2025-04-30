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

class mptReqBundle(implicit p: Parameters) extends XSBundle with MPTcacheparam {//mpt io interface req and resp , id is not used in ptw 
    val reqPA = UInt(ppnLen.W)
    val id = UInt(mptSourceWidth.W)
    val mptonly = Bool()//1bit 控制逻辑，对mptchecker本身无用，用于mptchecker返回时的l2tlb 控制
}

class mptRespBundle(implicit p: Parameters) extends XSBundle with MPTcacheparam {
    val af = Bool()
    val mptperm = UInt(Perm_LEN.W)
    val contigous_perm = Bool()//仅对非H 拓展l0有效
    //表示连续8项perm一致； 无法做到像l0pte一样按照位压缩（8位 valididx），因为其gva->hpa映射关系并非线性(比如 gva->hpa的 ppn_low 不是1->1 2->2 而是 1->7 2->3)
    val permIsNAPOT = Bool()
    val id = UInt(mptSourceWidth.W)
    val mptlevel =  UInt(2.W)//4
    val mptonly = Bool()//1bit 控制逻辑，对mptchecker本身无用，用于mptchecker返回时的l2tlb 控制
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
    val  access = Flipped(ValidIO(UInt(setNum.W)))
    val replace = Output(UInt(setNum.W))
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


class mptDATA (implicit p: Parameters) extends XSBundle with MPTcacheparam {
    val DATA =  UInt(Perm_LEN.W) 
    def apply(iDATA:UInt) :Unit={
        this.DATA:=iDATA//zero extended 
    }
    def getPPN : UInt ={//get PPN
        this.DATA(ppnLen-1,0)
    }
    def getADDR(offset: UInt):UInt={
        Cat(this.getPPN,Cat(offset,0.U(3.W)))//2|3 byte =64bit
    } 
    def extractPerm(select: UInt): (UInt) = {//extract XWR using 4bit offset
    // cal start end and extract
        (this.DATA>>(select*3.U))(2,0)// not quite sure what kind of crap will be synthesized. I meant it to be a binary mux
    }
}

class mptEntry (implicit p: Parameters) extends XSBundle with MPTcacheparam {
    val N = Bool()
    val DATA = new mptDATA()
    val L= Bool()
    val V= Bool()
    def apply(sMEM_RESP:UInt):Unit={
        this.V:= (sMEM_RESP(0)===1.U)
        this.L:= (sMEM_RESP(1)===1.U)
        this.N:= (sMEM_RESP(63)===1.U)
        this.DATA.apply(sMEM_RESP(57,10))//xiangshan only support 48bit PA, so PPN only needs 36
    }
    def isValid:Bool={
        this.V
    }
    
    def isLeaf:Bool={
        this.L
    }

    def getADDR(offset: UInt):UInt={
        this.DATA.getADDR(offset)
 
    }
}


class mptCacheTAG ( tagLen: Int, isSP:Boolean = false, isL0:Boolean = false) (implicit p: Parameters) extends XSBundle with MPTcacheparam {//<=
    //val sdid = if(SDID_cache_store_en) Some(UInt(SDIDLen.W)) else None //6.W 没用
    if(!isL0){val valid = Bool()}
    val tag = UInt(tagLen.W)
    val level = if(isSP) UInt(3.W) else UInt(0.W)
    val valid = Bool()
    def hit(ppn: UInt ): Bool={
        tag === ppn(ppnLen-1,ppnLen-tagLen)//tag =5, (47,43)
    }
    def hitsp (ppn: UInt ): Bool ={
        val hitl3 = (this.tag(tagLen-1,tagLen-mptL3TagLen) === ppn(ppnLen-1,ppnLen-mptL3TagLen))//tag =5, (47,43)
        val hitl2 = (this.tag(tagLen-1,tagLen-mptL2TagLen)  === ppn(ppnLen-1,ppnLen-mptL2TagLen))
        val hitl1 = (this.tag === ppn(ppnLen-1,ppnLen-tagLen)) 
        val hotval = Mux1H(this.level, Seq(hitl3,hitl2, hitl1))//it is a tuple scala> 1 -> 2 res0: (Int, Int) = (1,2)
        hotval 
    }
}
class mptCacheData( isPERMs: Boolean= false)  (implicit p: Parameters) extends XSBundle with MPTcacheparam {
    val data = if(isPERMs) UInt(Perm_LEN.W)  else UInt(ppnLen.W) //36.W
    def extractPerm(select: UInt): (UInt) = {//extract XWR using 4bit offset
    // cal start end and extract
    require(isPERMs ,"extractPerm is only valid when isPERMs is true")
    (this.data>>(select*3.U))(2,0)// not quite sure what kind of crap will be synthesized. I meant it to be a binary mux
    }
}

class mptCacheL0(implicit p: Parameters)  extends XSBundle with MPTcacheparam {
    val cacheData   = new mptCacheData(isPERMs=true)
    val tag         = new mptCacheTAG(tagLen = mptL0TagLen,isL0 = true )
}

class MPTcacheREQ (implicit p: Parameters) extends XSBundle with MPTcacheparam {
    val mptonly = Bool()
    val REQ_PA= UInt(PAddrBits.W)
    val source = UInt(mptSourceWidth.W)
}
class MPTPipe (implicit p: Parameters) extends MPTcacheREQ { 
    val datavalid= Bool() 
    val flushcache =Bool()
}  

class refillBundle(implicit p: Parameters)  extends XSBundle with MPTcacheparam {
        val level = UInt(Level_LEN.W)
        val PA= UInt((PAddrBits- MptOff).W)
        val Data = new mptDATA()
        //val entry_error = Bool()
        val mpte_L =Bool() // is leaf? decide what cache is refilled
    }
class MPTCacheIO(implicit p: Parameters) extends MMUIOBaseBundle with MPTcacheparam{
    val req = Flipped(DecoupledIO(new MPTcacheREQ()))

    val resp_hit = ValidIO(new Bundle {// source is waiting for cache to resp
        val af = Bool()
        val PERM = UInt(3.W)
        val tlbcontigous_perm = Bool()//仅对非H 拓展l0有效
        val permIsNAPOT = Bool()
        val source= UInt(mptSourceWidth.W)
        val mptlevel = UInt(log2Up(Level_LEN).W)
        val mptonly = Bool()
        val reqPA= UInt(ppnLen.W)
    })

    val resp_miss = DecoupledIO(new Bundle {
        val hitLevel=UInt((Level_LEN).W)
        val ppn = UInt(ppnLen.W)//minsize is 4k,dont need 12bits offset
        val source= UInt(mptSourceWidth.W)
        val PA= UInt((ppnLen).W)
        val mptOnly = Bool()
    })
    
   val refill = Flipped(ValidIO(new refillBundle()))
    
}

class MPTCache (implicit p: Parameters) extends XSModule with MPTcacheparam {
    val io = IO(new MPTCacheIO)
    ////mfence signal
    val mfenceActive = WireInit(false.B)
    val PAFence= WireInit(false.B)
    //本mpt设计支持按pa刷新cache中的部分，刷新时除了叶节点外，同时也会把中间节点一并刷了(或许不用)
    switch(Cat(io.mfence.get.bits.rs2, io.mfence.get.bits.rs1).asUInt){ 
        is("b11".U) {
            PAFence:= (io.mfence.get.bits.id===io.csr.mmpt.sdid) && io.mfence.get.valid // 大概10层gate 延迟,无所谓
        }
        is("b01".U){
            PAFence:= io.mfence.get.valid
        }
        is("b10".U){
            mfenceActive:= (io.mfence.get.bits.id===io.csr.mmpt.sdid) && io.mfence.get.valid
        }
        is("b00".U){
            mfenceActive:= io.mfence.get.valid
        }
    }
    val flushAll = mfenceActive || io.csr.mmpt.changed
    val mpt_flush_reset = (reset.asBool || flushAll).asBool//当csr 变化或mfence，flush
    withReset (mpt_flush_reset){// 根据fence 信号把它全给刷了
        val pipeFlowEn= Wire(Bool())
        pipeFlowEn:= io.resp_miss.ready & (! io.refill.valid)
        // 根据是否mfence-PA 是否refill 切换 pipeline input
        val PAfenceInputs = Wire(new MPTPipe)
        PAfenceInputs.REQ_PA :=  io.mfence.get.bits.addr
        PAfenceInputs.source := 0.U 
        PAfenceInputs.datavalid := false.B   
        PAfenceInputs.flushcache := true.B   

        val ioInputs= Wire(new MPTPipe)
        ioInputs.REQ_PA := io.req.bits.REQ_PA
        ioInputs.source := io.req.bits.source        
        ioInputs.datavalid := io.req.fire
        ioInputs.flushcache := false.B

        val refilling = Wire(Bool())
        val pipeInputs = Wire(new MPTPipe)
        val stageReq = Pipe(pipeFlowEn,pipeInputs,1)  
        val stageDelay= Pipe(pipeFlowEn, stageReq.bits,1)
        val stageCheck= Pipe(pipeFlowEn, stageDelay.bits,1)
        val stageResp= Pipe(pipeFlowEn, stageCheck.bits,1)
        pipeInputs := Mux(PAFence, PAfenceInputs, Mux(refilling,stageResp.bits,ioInputs))

        val ready = RegInit(true.B)
        io.req.ready := io.resp_miss.ready && !PAFence && !refilling //blocking
        //init cache tag
        val l3tag = Reg(Vec(l3Size, new mptCacheTAG(tagLen = mptL3TagLen)))
        val l2tag = Reg(Vec(l2Size, new mptCacheTAG(tagLen = mptL2TagLen)))
        val l1tag = Reg(Vec(l1Size,  new mptCacheTAG(tagLen = mptL1TagLen))) 
 
        val sptag = Reg(Vec(spSize, new mptCacheTAG(tagLen = mptspTagLen,isSP = true)))

        val l3data = Reg(Vec(l3Size, new mptCacheData()))
        val l2data = Reg(Vec(l2Size, new mptCacheData()))
        val l1data = Reg(Vec(l1Size,  new mptCacheData())) 
        val spdata = Reg(Vec(spSize, new mptCacheData(isPERMs = true)))  
        val l0data = Module(new SRAMTemplateMPT(new mptCacheL0(),set =  l0nSets, way = l0nWays))//1clk delay from req to resp
        val l0valid = Reg(Vec(l0nSets,Vec(l0nWays, Bool())))

        val mptcachel3replace = Module(new PLRUOH(log_ways = log2Up(l3Size))).io
        val mptcachel2replace = Module(new PLRUOH(log_ways = log2Up(l2Size))).io
        val mptcachel1replace = Module(new PLRUOH(log_ways = log2Up(l1Size))).io
        val mptcachel0replace = Module(new PLRUOHSet(sets_log2 = log2Up(l0nSets),log_ways = log2Up(l0nWays))).io
        val mptcachespreplace = Module(new PLRUOH(log_ways = log2Up(spSize))).io
        //alloc replacement policy,use PLRU with Onehot in/out

        val (l3hit,l3hitPPN) ={
            val hitVecT = l3tag.map{case(x) =>x.hit(stageReq.bits.REQ_PA) && x.valid}//hit when valid and tag equal stagereq
            when(stageReq.bits.flushcache)  {  // 一轮清空fence valid
                hitVecT.zipWithIndex.map{case(x,i)=> 
                    when(x){l3tag(i).valid := false.B}
                }
            }
            val hitVec = RegEnable(VecInit(hitVecT), stageReq.bits.datavalid) //ready at stage check，使用datavalid 而不是 stageReq.valid ，这样内部逻辑在pipe内项无效时就不会切换了，省点电
            //val hitData= ParallelPriorityMux(hitVec zip l3data)
            val hitData= RegEnable(Mux1H(hitVecT,l3data), stageReq.bits.datavalid)//we can use onehot mux, should be faster.
            val hit=RegEnable(hitVecT.reduce(_||_), stageReq.bits.datavalid)// 1 bit hit ,avaliable at stage delay after 2 or gates
            
            mptcachel3replace.access.bits:= hitVec.asUInt //assign hitVec to plru to update plru state ,miss(hitVec = h0) will not change the plru state 
            mptcachel3replace.access.valid:=  stageDelay.bits.datavalid //ready at stage check
            (hit,hitData)
            
        }

        val (l2hit,l2hitPPN) ={
            val hitVecT = l2tag.map{case(x) =>x.hit(stageReq.bits.REQ_PA) && x.valid}//hit when valid and tag equal stagereq
            when(stageReq.bits.flushcache)  {  // 一轮清空fence valid
                hitVecT.zipWithIndex.map{case(x,i)=> 
                    when(x){l2tag(i).valid := false.B}
                }
            }
            val hitVec = RegEnable(VecInit(hitVecT), stageReq.bits.datavalid) //ready at stage check
            //val hitData= ParallelPriorityMux(hitVec zip l3data)
            val hitData= RegEnable(Mux1H(hitVecT,l2data), stageReq.bits.datavalid)//we can use onehot mux, should be faster.
            val hit=RegEnable(hitVecT.reduce(_||_), stageReq.bits.datavalid)// 1 bit hit ,avaliable at stage delay after 2 or gates
            
            mptcachel2replace.access.bits:= hitVec.asUInt //assign hitVec to plru to update plru state ,miss(hitVec = h0) will not change the plru state 
            mptcachel2replace.access.valid:=  stageDelay.bits.datavalid //ready at stage check
            (hit,hitData)
        }

        val (l1hit, l1hitPPN) ={
            val hitVecT = l1tag.map{case(x) =>x.hit(stageReq.bits.REQ_PA) && x.valid}//hit when valid and tag equal stagereq
            when(stageReq.bits.flushcache)  {  // 一轮清空fence valid
                hitVecT.zipWithIndex.map{case(x,i)=> 
                    when(x){l1tag(i).valid := false.B}
                }
            }            
            val hitVec = RegEnable(VecInit(hitVecT), stageReq.bits.datavalid) //ready at stage check
            //val hitData= ParallelPriorityMux(hitVec zip l3data)
            val hitData= RegEnable(Mux1H(hitVecT,l1data), stageReq.bits.datavalid)//we can use onehot mux, should be faster.
            val hit=RegEnable(hitVecT.reduce(_||_), stageReq.bits.datavalid)// 1 bit hit ,avaliable at stage delay after 2 or gates
            
            mptcachel1replace.access.bits:= hitVec.asUInt //assign hitVec to plru to update plru state ,miss(hitVec = h0) will not change the plru state 
            mptcachel1replace.access.valid:=  stageDelay.bits.datavalid //ready at stage check        
            (hit,hitData)

        }
        /////////////////////////// gen addr hit(l3-l1) at stage check
        //val(hitAddrLevelT,hitAddrT)=PriorityMux(Seq(l1hit,l2hit,l3hit),Seq(("b001".U,l1hitPPN),("b010".U, l2hitPPN),("b100".U,l3hitPPN))) 官方的PriorityMux 会在Select none 给出h0，但我要其它的default value
        val missLevel = Mux(io.csr.mmpt.mode === 2.U,"b1000".U,"b0100".U)//enablesmmpt52 = true, 0 delay since io.csr.mmpt.mode will not change during cache read
        val hitAddrLevelT= Mux(l1hit,"b0001".U,Mux(l2hit,"b0010".U,Mux(l3hit,"b0100".U,missLevel)))
        val hitAddrDataT= Mux(l1hit,l1hitPPN.data,Mux(l2hit,l2hitPPN.data,Mux(l3hit,l3hitPPN.data,io.csr.mmpt.ppn(ppnLen-1,0))))
        val hitAddrData= RegEnable(hitAddrDataT,stageDelay.bits.datavalid) 
        val hitAddrLevel=RegEnable(hitAddrLevelT,stageDelay.bits.datavalid)
        
        /////////////////////////// 
    
        val (l0hit, l0hitPERMs,l0permtlbcompress,l0permIs64kNAPOT) ={
            val idx = getl0set(pipeInputs.REQ_PA) //..    
            
            l0data.io.r.req.bits.apply(setIdx = idx)//.. 0 delay 相当于和stagereq的reg同时收到valid请求
            l0data.io.r.req.valid:= pipeInputs.datavalid|| pipeInputs.flushcache//read and write at the same time will not cause error, but read is invalid 

            val l0validReg =  RegEnable(l0valid(getl0set(stageReq.bits.REQ_PA)), stageReq.bits.datavalid|| stageReq.bits.flushcache)
            val data_resp = RegEnable(l0data.io.r.resp.data, stageReq.bits.datavalid|| stageReq.bits.flushcache)//data avaliable at stage delay
            val settag = data_resp.map(_.tag)
            val setdata = data_resp.map(_.cacheData)//4 entry+tag
            //some wire
            val hitVecT = settag.zip(l0validReg).map{case(x,v)=>x.hit(stageDelay.bits.REQ_PA) && v}//hit when valid and tag equal
            
            //delay (29 bit===):(1xnor + 5*and), (&& valid):(1 and) total 7
            //MfencePA
            when(stageDelay.bits.flushcache)  {  // 一轮清空fence valid
                hitVecT.zipWithIndex.map{case(x,i)=> 
                    when(x){l0valid(getl0set(stageDelay.bits.REQ_PA))(i) := false.B}
                }
            }

            //
            val hitVec = RegEnable(VecInit(hitVecT),stageDelay.bits.datavalid)//valid at stage check
            val hitData= Mux1H(hitVecT,setdata)//we use onehot mux, should be faster than ParallelPriorityMux. delay:log2(4)*2=4
            val hitDataReg= RegEnable(hitData,stageDelay.bits.datavalid)//valid at stage check, total delay 11 gates
            val hit=RegEnable(hitVecT.reduce(_||_),stageDelay.bits.datavalid)// 4-> 1 bit hit 

            val hitPERMsT= hitDataReg.extractPerm(stageCheck.bits.REQ_PA(15,12))//always 15:12 delay log2(16)*3=12 gates

            mptcachel0replace.access.bits:= hitVec.asUInt //assign hitVec to plru to update plru state ,miss(hitVec = h0) will not change the plru state 
            mptcachel0replace.access.valid:=  stageCheck.bits.datavalid // processing at stage check, ready at stage resp
            mptcachel0replace.idx:= getl0set(stageCheck.bits.REQ_PA)

            val PermsAsVec = Wire(Vec(16,UInt(3.W))) //perm xwr bits, total 16 xwrs in one mpte
            for (i <- 0 until 16) {PermsAsVec(i):= hitDataReg.data((2+ i*3), (i*3))}
            val PermsEqual = Wire(Vec(16-1,Bool()))
            for (i <- 0 until 16-1) {PermsEqual:= PermsAsVec(i+1) === PermsAsVec(i)}//delay 1XNOR + 2 and gates = 3   
            val low8PermsAllEqual = PermsEqual.slice(0,7).reduce(_&&_) //=PermsEqual(6,0), delay 3
            val high8PermsAllEqual = PermsEqual.slice(8,15).reduce(_&&_) //=PermsEqual(14,8)
            val allequal = low8PermsAllEqual && high8PermsAllEqual && PermsEqual(7) //Delay 2
            val tlbcompress= Mux( stageCheck.bits.REQ_PA(15,12) < 8.U,low8PermsAllEqual, high8PermsAllEqual)//delay 3
            
            (hit,RegEnable(hitPERMsT,stageCheck.bits.datavalid),RegEnable(tlbcompress,stageCheck.bits.datavalid),RegEnable(allequal,stageCheck.bits.datavalid))//ready at stage resp,hit reaady at stage check
        }
    
        val (sPhit,sPhitPERMs,sppermIsNAPOT,splevel) = {
            val hitVecT = sptag.map(x=>x.hitsp(stageReq.bits.REQ_PA) && x.valid)//hit when valid and tag equal delay 7 + mux1h delay 4 gates
            when(stageReq.bits.flushcache)  {  // 一轮清空fence valid
                hitVecT.zipWithIndex.map{case(x,i)=> 
                    when(x){sptag(i).valid := false.B}
                }
            }

            val hitVec = RegEnable(VecInit(hitVecT), stageReq.bits.datavalid) //ready at stage delay
            ////////
            val levelVec = sptag.map(x=>x.level)
            val level = Mux1H(hitVec,levelVec)//ready at stage delay, require cache to be consistent
            val levelreg= RegEnable(level,stageDelay.bits.datavalid)   
            val levelUInt = Wire(UInt(2.W))
            levelUInt:= OHToUInt(Cat(levelreg,0.U(1.W)))   

            val extractOffset= Mux1H( level, Seq(
            stageDelay.bits.REQ_PA(15+9*3,12+9*3),
            stageDelay.bits.REQ_PA(15+9*2,12+9*2),
            stageDelay.bits.REQ_PA(15+9,12+9)
            ))

            val extractOffsetReg= RegEnable(extractOffset,stageDelay.bits.datavalid) //ready at stage check

            //val hitData= ParallelPriorityMux(hitVec zip l3data)
            val hitData = Mux1H(hitVec,spdata)//we can use onehot mux, should be faster.
            val hitDataReg = RegEnable(hitData,stageDelay.bits.datavalid)//valid at stage check, total delay 11 gates
            val hitPERMsT = hitDataReg.extractPerm(extractOffsetReg)//always 15:12 delay log2(16)*3=12 gates
            val hit=RegEnable(hitVec.reduce(_||_), stageDelay.bits.datavalid)// 1 bit hit 
            
            mptcachespreplace.access.bits:= hitVec.asUInt //assign hitVec to plru to update plru state ,miss(hitVec = h0) will not change the plru state 
            mptcachespreplace.access.valid:=  stageDelay.bits.datavalid //ready at stage check
            
            val PermsAsVec = Wire(Vec(16,UInt(3.W))) //perm xwr bits, total 16 xwrs in one mpte
            for (i <- 0 until 16) {PermsAsVec(i):= hitDataReg.data((2+ i*3), (i*3))}
            val PermsEqual = Wire(Vec(16-1,Bool()))
            for (i <- 0 until 16-1) {PermsEqual:= PermsAsVec(i+1) === PermsAsVec(i)}//delay 1XNOR + 2 and gates = 3   
            val allequal = PermsEqual.reduce(_&&_) //=PermsEqual, delay 4

            (hit,RegEnable(hitPERMsT,stageCheck.bits.datavalid),RegEnable(allequal,stageCheck.bits.datavalid),RegEnable(levelUInt,stageCheck.bits.datavalid))//ready at stage resp,hit reaady at stage check
        }
    ///////gen perms hit l0 sp at stage check 

        val hitperms = sPhit || l0hit
        io.resp_hit.valid := RegEnable(hitperms & stageCheck.bits.datavalid,stageCheck.valid)//无论是否datavalid都读入，data invalid 则hit也invalid，此时的hitperms实为上一个pipe的结果
        val (sPhitReg,l0hitReg) = (RegEnable(sPhit,stageCheck.bits.datavalid),RegEnable(l0hit,stageCheck.bits.datavalid))
        io.resp_hit.bits.PERM := Mux1H(Seq(sPhitReg,l0hitReg),Seq(sPhitPERMs,l0hitPERMs)) //1 mux at output, 2 gates, should be fine
        io.resp_hit.bits.source := stageResp.bits.source //转一圈回去
        io.resp_hit.bits.mptonly:= stageResp.bits.mptonly
        io.resp_hit.bits.tlbcontigous_perm:= l0permtlbcompress
        io.resp_hit.bits.permIsNAPOT:=  Mux1H(Seq(sPhitReg,l0hitReg),Seq(sppermIsNAPOT,l0permIs64kNAPOT)) 
        io.resp_hit.bits.af:=false.B//entry in mpt cache is always valid 
        io.resp_hit.bits.mptlevel:= Mux1H(Seq(sPhitReg,l0hitReg),Seq(splevel,0.U(2.W)))//splevel is converted to binary for l1/l2tlb level compare with s1pte and s2pte


        io.resp_miss.valid := RegEnable(!hitperms &  stageCheck.bits.datavalid,stageCheck.valid)//无论是否datavalid都读入
        io.resp_miss.bits.hitLevel := RegEnable(hitAddrLevel,stageCheck.bits.datavalid)
        io.resp_miss.bits.ppn := RegEnable(hitAddrData,stageCheck.bits.datavalid)
        io.resp_miss.bits.source := stageResp.bits.source
        io.resp_miss.bits.mptOnly:= stageResp.bits.mptonly
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
        val l3RefillEn = io.refill.bits.level(3).asBool & (!io.refill.bits.mpte_L) & io.refill.valid
        val rfl3Tag = io.refill.bits.PA(PAddrBits- MptOff-1, PAddrBits- MptOff- mptL3TagLen)
        val l3VictimWay = mptcachel3replace.replace// ready after idx is set , OH encoding

        val l2RefillEn = io.refill.bits.level(2).asBool & (!io.refill.bits.mpte_L)& io.refill.valid
        val rfl2Tag = io.refill.bits.PA(PAddrBits- MptOff-1, PAddrBits- MptOff- mptL2TagLen)
        val l2VictimWay = mptcachel2replace.replace// ready after idx is set , OH encoding

        val l1RefillEn = io.refill.bits.level(1).asBool & (!io.refill.bits.mpte_L)& io.refill.valid
        val rfl1Tag = io.refill.bits.PA(PAddrBits- MptOff-1, PAddrBits- MptOff- mptL1TagLen)
        val l1VictimWay = mptcachel1replace.replace// ready after idx is set , OH encoding

        val l0RefillEn = io.refill.bits.level(0).asBool & (io.refill.bits.mpte_L) &  io.refill.valid
        val rfl0Tag = io.refill.bits.PA(PAddrBits- MptOff-1, PAddrBits- MptOff- mptL0TagLen)
        val rfl0SetIdx = io.refill.bits.PA(PAddrBits- MptOff- mptL0TagLen-1, 0)
        val l0VictimWay = mptcachel0replace.replace// ready after idx is set , OH encoding


        val spRefillEn = (!io.refill.bits.level(0).asBool) & io.refill.bits.mpte_L & io.refill.valid
        val rfspTag = io.refill.bits.PA(PAddrBits- MptOff-1, PAddrBits- MptOff- mptspTagLen)
        val spVictimWay = mptcachespreplace.replace // 

        ///write data into cache 1 cycle 
        val l0Wdata = Wire(new mptCacheL0()) // 0 delay ,wire signal assignment
        l0Wdata.tag.tag := rfl0Tag
        l0Wdata.tag.valid := true.B
        l0Wdata.cacheData.data := io.refill.bits.Data.DATA // 等有空把class 的子类父类重写一遍
        l0data.io.w.req <> DontCare //default val for write channel is invalid 
        l0data.io.w.req.valid := false.B
        when (l0RefillEn) {
            l0data.io.w.apply(
            valid = true.B, //valid when refill
            setIdx = rfl0SetIdx,
            data = l0Wdata,
            waymask = l0VictimWay
            )
            mptcachel0replace.idx:= rfl0SetIdx //覆盖pipeline的赋值，这里不太明显，或许可以把信号单独拎出来
            //refill时切换plru输入至refill数据并立即更新，4way更新延迟：2 gates，32组idx切换3 gates，l0 refillEn 1 gates,mux refillEn切换输入 3 gates
            mptcachel0replace.access.bits:= l0VictimWay
            mptcachel0replace.access.valid:= true.B
        }

        when (l3RefillEn) {
            for (i <- 0 until l3Size) {
                when(l3VictimWay(i)===1.U){
                    l3tag(i).tag := rfl3Tag 
                    l3tag(i).valid := true.B
                    l3data(i).data:= io.refill.bits.Data.getPPN 
                }
            }
            mptcachel3replace.access.bits:= l3VictimWay
            mptcachel3replace.access.valid:= true.B
        }

        when (l2RefillEn) {
            for (i <- 0 until l2Size) {
                when(l2VictimWay(i)===1.U){
                    l2tag(i).tag := rfl2Tag 
                    l2tag(i).valid := true.B
                    l2data(i).data:= io.refill.bits.Data.getPPN 
                }
            }
            mptcachel2replace.access.bits:= l2VictimWay
            mptcachel2replace.access.valid:= true.B
        }
        when (l1RefillEn) {
             for (i <- 0 until l1Size) {
                when(l1VictimWay(i)===1.U){
                    l1tag(i).tag := rfl1Tag 
                    l1tag(i).valid := true.B
                    l1data(i).data:= io.refill.bits.Data.getPPN 
                }
            }
            mptcachel1replace.access.bits:= l1VictimWay
            mptcachel1replace.access.valid:= true.B
        }
        when (spRefillEn) {
            /*spVictimWay.zipWithIndex.map{case(en,i) => // update cache content
                when(en){*/
            for (i <- 0 until spSize) {
                when(spVictimWay(i)===1.U){    
                    sptag(i).tag    := rfspTag 
                    sptag(i).valid  := true.B
                    sptag(i).level  := io.refill.bits.level(3,1)
                    spdata(i).data  := io.refill.bits.Data.DATA 
                }
            }
            mptcachespreplace.access.bits:= spVictimWay
            mptcachespreplace.access.valid:= true.B
        }
    }
}
////////////////////////////////////////// MSHR START ///////////////////////////////////////////////////////////////////////////////
class MSHRreg()(implicit p: Parameters) extends XSBundle with MPTcacheparam {
    val HIT_ADDR =  UInt(ppnLen.W) 
    val level=UInt((Level_LEN).W)
    val REQ_PA= UInt((PAddrBits- MptOff).W)
    val valid = Bool()
}

class permTable() (implicit p: Parameters) extends XSBundle with MPTcacheparam {
    val source = UInt(mptSourceWidth.W)
    val offset= UInt((MptOff-12).W) //offset to decide which perm to use
    val tag =UInt(1.W)
    val mptonly = Bool()
    //val valid=Bool() we are using a queue valid is not needed
}

class mshrToTWReqBundle(implicit p: Parameters) extends XSBundle with MPTcacheparam {
    val hitAddr =  UInt(ppnLen.W)
    val reqPA = UInt((PAddrBits- MptOff).W)
    val hitLevel = UInt(Level_LEN.W)
}
class TWtomshrRespBundle(implicit p: Parameters) extends XSBundle with MPTcacheparam {
        val PERMs = new mptDATA()
        val mpttwLevel = UInt(Level_LEN.W)
        //val reqPA = UInt((PAddrBits- MptOff).W)
        val AF = Bool()
}
class MSHRIO(implicit p: Parameters) extends XSBundle with MPTcacheparam {
    val missCache =Flipped(DecoupledIO(new Bundle {
        val hitLevel=UInt((Level_LEN).W)
        val hitAddr = UInt(ppnLen.W)//hit addr 
        val source= UInt(mptSourceWidth.W)
        val PA= UInt((ppnLen).W)//req pa minsize is 4k,dont need 12bits offset
        val mptOnly= Bool()//1bit control signal for tlb, does basically nothing in mptc
    }   ) )

    val twReq = DecoupledIO(new mshrToTWReqBundle())

    val twFin = Flipped(DecoupledIO(new TWtomshrRespBundle()))

    val resp = ValidIO(new Bundle {// source is waiting for cache to resp
        val AF = Bool()
        val mptlevel = UInt(Level_LEN.W)
        val PERM = UInt(3.W)
        val PERMtlbcompress = Bool()
        val permIsNAPOT = Bool()
        val mptonly = Bool()
        val reqPA = UInt(ppnLen.W)
        val source= UInt(mptSourceWidth.W)
    })

}

class MSHR(implicit p: Parameters) extends XSModule with MPTcacheparam {
    val io=IO(new MSHRIO)

    val fsmIDLE = Wire(Bool()) //when busy stop read and send(can still send? maybe) 
    val sendTwEn =  Wire(Bool())

    val TWResp = RegEnable(io.twFin.bits,io.twFin.fire)//store the tw resp to reg

    val MSHRreg0= Reg(Vec(2, new MSHRreg()))   //MSHR reg records PA
    val active = Reg(UInt(1.W)) //indicate the current FSM and wirte MSHR
    val sendActive= Wire(UInt(1.W))//

    val mshrRegFull = MSHRreg0.map(_.valid).reduce(_&&_)
    val mshrRegEmpty = !(MSHRreg0.map(_.valid).reduce(_||_))

    val permTableFIFO = Module(new Queue(new permTable() ,8)).io //FIFO queue,record offset

    val tableNotFull = permTableFIFO.enq.ready
    val tableNotEmpty = permTableFIFO.deq.valid
    io.missCache.ready := tableNotFull && !(mshrRegFull) && fsmIDLE //ready when both not full

    permTableFIFO.enq.valid := io.missCache.fire// 无论如何，fire时都要录入table
    permTableFIFO.enq.bits.source:= io.missCache.bits.source
    permTableFIFO.enq.bits.offset:= io.missCache.bits.PA(MptOff-offLen-1,0)//3-0 offset
    permTableFIFO.enq.bits.mptonly:= io.missCache.bits.mptOnly
    permTableFIFO.enq.bits.tag:= active
    when(io.missCache.fire & (MSHRreg0(active).REQ_PA =/= io.missCache.bits.PA(ppnLen-1, MptOff-offLen))){//when 4k addr does not repeat
        MSHRreg0(! active).HIT_ADDR := io.missCache.bits.hitAddr
        MSHRreg0(! active).level :=  io.missCache.bits.hitLevel
        MSHRreg0(! active).REQ_PA := io.missCache.bits.PA(ppnLen-1, MptOff-offLen)
        MSHRreg0(! active).valid :=  true.B
        permTableFIFO.enq.bits.tag:= !active
        when(mshrRegEmpty){//when empty,points to the newly written MSHR
            active:= !active
             
        }
    } 
    //mshr write logic end, write to not active mshr
    io.twReq.bits.hitAddr:=MSHRreg0(sendActive).HIT_ADDR
    io.twReq.bits.reqPA:=MSHRreg0(sendActive).REQ_PA
    io.twReq.bits.hitLevel:=MSHRreg0(sendActive).level
    io.twReq.valid:= MSHRreg0(sendActive).valid && sendTwEn
    //mshr send end, send the mshr which has been pointed by active to tw,repeat sending is not possible,since active will change as soon as the twresp is recorded
    
    val retPermOffset= Mux1H(Seq(//different level use different offset 
        TWResp.mpttwLevel(3)-> MSHRreg0(active).REQ_PA(9*3-1,9*3-4),
        TWResp.mpttwLevel(2)-> MSHRreg0(active).REQ_PA(9*2-1,9*2-4),
        TWResp.mpttwLevel(1)-> MSHRreg0(active).REQ_PA(9-1,9-4),
        TWResp.mpttwLevel(0)-> permTableFIFO.deq.bits.offset)) //read from table entry instead
    io.resp.bits.PERM :=TWResp.PERMs.extractPerm(retPermOffset)// mshr return bits when AF,return 000 not allow, else perm val 
    io.resp.bits.AF := TWResp.AF
    io.resp.bits.source := permTableFIFO.deq.bits.source
    io.resp.bits.mptonly := permTableFIFO.deq.bits.mptonly
    
    val PermsAsVec = Wire(Vec(16,UInt(3.W))) //perm xwr bits, total 16 xwrs in one mpte
    for (i <- 0 until 16) {PermsAsVec(i):= TWResp.PERMs.DATA((2+ i*3), (i*3))}
    val PermsEqual = Wire(Vec(16-1,Bool()))
    for (i <- 0 until 16-1) {PermsEqual:= PermsAsVec(i+1) === PermsAsVec(i)}//delay 1XNOR + 2 and gates = 3   
    val leftPermsAllEqual = PermsEqual.slice(0,7).reduce(_&&_) //=PermsEqual(6,0), delay 3
    val rightPermsAllEqual = PermsEqual.slice(8,15).reduce(_&&_) //=PermsEqual(14,8)
    io.resp.bits.permIsNAPOT := leftPermsAllEqual && rightPermsAllEqual && PermsEqual(7) //Delay 2
    io.resp.bits.PERMtlbcompress := Mux(permTableFIFO.deq.bits.offset<8.U,leftPermsAllEqual, rightPermsAllEqual)//delay 3

    io.resp.bits.mptlevel:= OHToUInt(TWResp.mpttwLevel) //convert to UInt
    io.resp.bits.reqPA := Cat(MSHRreg0(active).REQ_PA , permTableFIFO.deq.bits.offset)//return reqPa is MSHR tag + offset 
    val mshrRetAllL3 = MSHRreg0(0).REQ_PA(PAddrBits- MptOff - 1,PAddrBits- MptOff-mptL3TagLen) === MSHRreg0(1).REQ_PA(PAddrBits- MptOff - 1,PAddrBits- MptOff-mptL3TagLen)&&mshrRegFull
    //大页两种情况会继续return 1. mshr0/1 地址同属一个大页地址空间 mshrRetAllLn===true.B 并且都valid2 当前table项属于当前active mshr 
    val mshrRetAllL2 = MSHRreg0(0).REQ_PA(PAddrBits- MptOff - 1,PAddrBits- MptOff-mptL2TagLen) === MSHRreg0(1).REQ_PA(PAddrBits- MptOff - 1,PAddrBits- MptOff-mptL2TagLen)&&mshrRegFull
    val mshrRetAllL1 = MSHRreg0(0).REQ_PA(PAddrBits- MptOff - 1,PAddrBits- MptOff-mptL1TagLen) === MSHRreg0(1).REQ_PA(PAddrBits- MptOff - 1,PAddrBits- MptOff-mptL1TagLen)&&mshrRegFull
    val mshrAllowRetAll= Mux1H(Seq(
        TWResp.mpttwLevel(3)-> mshrRetAllL3,
        TWResp.mpttwLevel(2)-> mshrRetAllL2,
        TWResp.mpttwLevel(1)-> mshrRetAllL1,
        TWResp.mpttwLevel(0)-> false.B//4k addr len can not repeat
    )) //delay TODO***

    // mshr return valid using FSM(or maybe not,since it only has two states)

    object mshrstate extends ChiselEnum {
            val sIDLE , sProc = Value
        }
    import mshrstate._ 
    val curstate = RegInit(sIDLE)
    val nextstate = WireDefault(sIDLE)
    curstate:= nextstate// 2 proc FSM 

    nextstate := curstate
    io.twFin.ready := false.B
    fsmIDLE:= false.B
    permTableFIFO.deq.ready:= false.B
    io.resp.valid:= false.B
    sendActive:= active
    sendTwEn :=  false.B 
    switch(curstate) {
        is(sIDLE) {
            io.twFin.ready := true.B//can receive tw resp
            fsmIDLE:= true.B//can receive cache request 
            sendTwEn:= true.B
            when(io.twFin.fire){
                nextstate:= sProc
                //fsmIDLE:= false.B//disable cache req input
            }   
        }
        is(sProc) {
            when (! mshrAllowRetAll){ 
                sendTwEn:= true.B 
                sendActive := !active
            }//if valid, send tw the req without waiting the return perm to finish. only possible when not mshrAllowRetAll,大概快4clk吧，聊胜于无
            when (permTableFIFO.deq.valid && (mshrAllowRetAll || active === permTableFIFO.deq.bits.tag)){//there is something in the queue
                //大页两种情况会继续return 1. mshr0/1 地址同属一个大页地址空间 mshrRetAllLn===true.B 并且都valid2 当前table项属于当前active mshr          
                permTableFIFO.deq.ready:= true.B //pop queue until empty
                io.resp.valid:= true.B
            } .otherwise{
                nextstate:= sIDLE
                active:= !active
                when (mshrAllowRetAll) {
                    MSHRreg0(0).valid:=false.B
                    MSHRreg0(1).valid:=false.B
                }.otherwise{
                    MSHRreg0(active).valid:=false.B
                }
            }
        }
    }
}


class mptTWIO(implicit p: Parameters) extends MMUIOBaseBundle with HasPtwConst {
    val req = Flipped(DecoupledIO(new mshrToTWReqBundle()))
    
    val resp = DecoupledIO(new TWtomshrRespBundle())

    val mem = new Bundle {
        val req = DecoupledIO(new Bundle { val addr = UInt(PAddrBits.W)})
        val resp = Flipped(ValidIO(UInt(XLEN.W)))//改片选
        //val mask = Input(Bool()) dont need？ 
    }

    val pmp = new Bundle {
        val req = ValidIO(new PMPReqBundle())
        val resp = Flipped(new PMPRespBundle())
    }
    val refill = ValidIO(new refillBundle()) 

}

 
class MPTTW (implicit p: Parameters) extends XSModule with MPTcacheparam{
    val io=IO(new mptTWIO)
    val mem=io.mem 
    
    

    val flush=io.mfence.get.valid || io.csr.mmpt.changed
    val mpt_flush_reset= (reset.asBool || flush).asBool//当csr 变化或mfence，flush
    withReset (mpt_flush_reset){//
        ////////////////
        val pa = RegEnable(io.req.bits.reqPA, 0.U,io.req.fire)//收到的req pa,存入 reg, 用来生成pn123 offset 合成表地址
        io.refill.bits.PA := pa
        ////////////////////////////////////////////////////////////////////
        val mpte_resp =Wire(new mptEntry())
        mpte_resp.apply(mem.resp.bits)// mem 返回的转化mpte，存入 mpte_data
        // 定义level寄存器
        val set_level= Wire(Bool())
        val set_pmp_check_level= Wire(Bool())
        val nextlevel = Wire(UInt(Level_LEN.W))
        val nextpmp_check_level = Wire(UInt(Level_LEN.W))

        val level = RegEnable(nextlevel,"b1000".U(Level_LEN.W),set_level)
        val pmp_check_level = RegEnable(nextpmp_check_level,"b1000".U(Level_LEN.W),set_pmp_check_level)

 


        //////

        val mpte_data = Reg(new mptDATA())//存返回的perm/下级addr 或者 发送来的req addr enter， 用来返回perms 或者 与pa 合成下级页表
        io.resp.bits.PERMs:= mpte_data// output alloc
        io.refill.bits.Data:= mpte_data// output alloc
        val mpte_L=RegEnable(mpte_resp.isLeaf,false.B,io.mem.resp.valid)
        io.refill.bits.mpte_L := mpte_L// tell cache if the current refill is leaf node 
        val mpte_invalid=RegEnable(!mpte_resp.isValid,false.B,io.mem.resp.valid)//1 level not on top of mem.resp 
        val RSV_ERROR=RegEnable(mem.resp.bits(9,2).orR,false.B,io.mem.resp.valid)//max 3 level or gate on top of mem.resp，NON ZERO error of mtpe
        //val RSV_ERROR2=RegEnable(mem.resp.bits(62)===1.U ,false.B,io.mem.resp.valid)
        //val RSV_ERROR3=RegEnable(( mpte_resp.isLeaf && mem.resp.bits(61:58).orR),false.B,io.mem.resp.valid)
        val RSV_ERROR2=RegEnable(mem.resp.bits(62,58).orR,false.B,io.mem.resp.valid)// 地址仅48位，高位为0，中间节点一样可以用同样的范围查zero
        val RSV_ERROR3=false.B
        when(io.req.fire) {
            mpte_data.apply(io.req.bits.hitAddr)
        }.elsewhen(io.mem.resp.valid){
            mpte_data:=mpte_resp.DATA
        }

        val pn=Wire(UInt(9.W)) //用level 和 pa 生成pn
        pn:=(Fill (9,level(3)) & Cat(0.U(4.W),pa(47-MptOff,43-MptOff))) | (Fill (9,level(2)) & pa(42-MptOff,34-MptOff)) | (Fill (9,level(1)) & pa(33-MptOff,25-MptOff)) | (Fill (9,level(0)) & pa(24-MptOff,16-MptOff))

        //pn:=Mux1H(Seq())

        //3 layers of gate logic select the coresponding PN[i] based on cur level,just a onehot mux 
        val mem_addr = mpte_data.getADDR(pn)//生成访问的addr， cat wire 0 延迟
        io.mem.req.bits.addr:= mem_addr
        //////////////////////////////////////////////////////////////// PMP 可能的时序问题， mem 返回值直接PMP check?事先预防，先打一拍
        io.pmp.req.valid:= DontCare 
        io.pmp.req.bits.addr:= Mux(io.mem.resp.valid, mpte_resp.getADDR(pn), mem_addr)//should be safer than just := mem_addr
        //io.pmp.req.bits.cmd := TlbCmd.read // uncomment 
        //io.pmp.req.bits.size := 3.U // TODO: fix it
        ////AF logic
        val pmp_fail= (!mpte_L)&&(io.pmp.resp.ld || io.pmp.resp.mmio) //PMP delay unknown 
        val entry_error= mpte_invalid|| RSV_ERROR|| RSV_ERROR2 || RSV_ERROR3 ||((!mpte_L) && level===0.U)//level==0 non leaf, zero=/=0,pmp fail,invalid casue AF
        val AF= entry_error|| pmp_fail//pmp fail also cause AF
       
        io.resp.bits.mpttwLevel:= Mux(pmp_fail,pmp_check_level,level)//pmp_fail return next level,else cur level
        io.resp.bits.AF:= AF    

        io.refill.bits.level:= level
        // pmp fail will not be recorded(if the root addr+ pn[i] cause pmp fail does not necessarily mean that the root addr + other offset will cause pmp fail, so entry will be refilled as a normal intermidiate node)
        //////////////////////////////FSM

    object mystate extends ChiselEnum {
            val sIDLE , sMEM_REQ, sMEM_RESP, sADDR_PROC, sMSHR_RETURN = Value
        }
    import mystate._
    
        //val sIDLE :: sMEM_REQ :: sMEM_RESP :: sADDR_PROC :: sMSHR_RETURN  :: Nil = Enum(5)
        val curstate = RegInit(sIDLE)
        val nextstate = WireDefault(sIDLE)
        curstate:= nextstate// 2 proc FSM 
        //fsm start
            mem.req.valid := false.B
            io.req.ready:= false.B
            nextstate := curstate
            set_level:= false.B
            set_pmp_check_level:=false.B
            nextlevel:=level>> 1.U //onehotcounter-1 只用一个就行 不用aflevel***改!!! 
            nextpmp_check_level:=pmp_check_level>> 1.U
            io.refill.valid:= false.B
            io.resp.valid:= false.B
        //default val
            switch(curstate) {
                is(sIDLE) {
                    io.req.ready:= true.B
                    when(io.req.fire){//fire 不是信号，是 ready&valid 把它当信号用会出错
                        set_pmp_check_level:=true.B
                        nextlevel:= io.req.bits.hitLevel
                        nextpmp_check_level:=io.req.bits.hitLevel
                        nextstate := sMEM_REQ//to mem req if fire 
                    }
                }
                is(sMEM_REQ) {
                    mem.req.valid:= true.B//req valid when not fire                    
                  
                    when(io.mem.req.fire) {//just waiting, timing safe
                        nextstate := sMEM_RESP //to wait resp
                    }.otherwise{
 
                    }
                }
                is(sMEM_RESP) {//unknown in delay,timing?
                    when(io.mem.resp.valid) {//do nothing,delay one cycle OPTPOINT*
                    nextstate := sADDR_PROC
                    set_pmp_check_level:= true.B
                    }
                }
                is(sADDR_PROC) {//known delay
                // 处理返回的节点
                    when(AF||mpte_L){//out delay unknown 
                        nextstate :=sMSHR_RETURN    //OPTPOINT*
                    }.otherwise{
                        io.refill.valid:= true.B//start refill
                        set_level:=true.B
                        nextstate :=sMEM_REQ    //OPTPOINT*
                    }      
                }
                is(sMSHR_RETURN) {
                    io.resp.valid:= true.B
                    when(io.resp.fire) {
                        nextstate := sIDLE
                    }
                }
            }
        //fsm end

         
    }
}

class mptCheckerIO(implicit p: Parameters) extends MMUIOBaseBundle with HasPtwConst {
val mem = new Bundle {
    val req = DecoupledIO(new L2TlbMemReqBundle())
    val resp = Flipped(DecoupledIO(new Bundle {
      //val id = Output(UInt(bMemID.W)) 只有一个接口,不需要区分
    val value = Output(UInt(XLEN.W))//mpttw 
    }))
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
    val mptCacheInst    = (new MPTCache()).io
    val mptTWInst       = (new MPTTW()).io
    val mshrInst        = (new MSHR()).io
 
    mptCacheInst.csr <> io.csr // 
    mptCacheInst.mfence.get <> io.mfence.get // 
    
    mptTWInst.csr <> io.csr // 
    mptTWInst.mfence.get <> io.mfence.get // 
    

    //cache请求输入mptcache
    mptCacheInst.req.bits.mptonly:= io.req.bits.mptonly//need some fix 
    mptCacheInst.req.bits.REQ_PA := io.req.bits.reqPA
    mptCacheInst.req.bits.source := io.req.bits.id
    mptCacheInst.req.valid:=  io.req.valid
    io.req.ready:= mptCacheInst.req.ready
    //cache hit/mshr结果返回，根据mshr valid 切换
 

    val mptReturn = Wire(new mptRespBundle())
    mptReturn.mptperm := Mux(mshrInst.resp.valid, mshrInst.resp.bits.PERM, mptCacheInst.resp_hit.bits.PERM) 
    mptReturn.contigous_perm := Mux(mshrInst.resp.valid, mshrInst.resp.bits.PERMtlbcompress, mptCacheInst.resp_hit.bits.tlbcontigous_perm)
    mptReturn.id := Mux(mshrInst.resp.valid, mshrInst.resp.bits.source, mptCacheInst.resp_hit.bits.source)
    mptReturn.mptlevel:= Mux(mshrInst.resp.valid, mshrInst.resp.bits.mptlevel, mptCacheInst.resp_hit.bits.mptlevel)
    mptReturn.mptonly:= Mux(mshrInst.resp.valid, mshrInst.resp.bits.mptonly, mptCacheInst.resp_hit.bits.mptonly)
    mptReturn.reqPA:= Mux(mshrInst.resp.valid, mshrInst.resp.bits.reqPA, mptCacheInst.resp_hit.bits.reqPA)
    mptReturn.af:=  Mux(mshrInst.resp.valid, mshrInst.resp.bits.AF, mptCacheInst.resp_hit.bits.af)
    mptReturn.permIsNAPOT :=  Mux(mshrInst.resp.valid, mshrInst.resp.bits.permIsNAPOT, mptCacheInst.resp_hit.bits.permIsNAPOT)

    io.resp.valid := mshrInst.resp.valid||mptCacheInst.resp_hit.valid
    io.resp.bits <> mptReturn
    //cache miss 发送mshr
    mshrInst.missCache.bits.mptOnly:=  mptCacheInst.resp_miss.bits.mptOnly
    mshrInst.missCache.bits.hitLevel:= mptCacheInst.resp_miss.bits.hitLevel
    mshrInst.missCache.bits.hitAddr:= mptCacheInst.resp_miss.bits.ppn
    mshrInst.missCache.bits.source:=  mptCacheInst.resp_miss.bits.source
    mshrInst.missCache.bits.PA:= mptCacheInst.resp_miss.bits.PA
    mshrInst.missCache.valid:= mptCacheInst.resp_miss.valid
    mptCacheInst.resp_miss.ready:= mshrInst.missCache.ready
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

    mptTWInst.mem.resp.bits:= io.mem.resp.bits.value//改宽度
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