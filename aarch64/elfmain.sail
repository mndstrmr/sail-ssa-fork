$include <elf.sail>

val read_register = "reg_deref" : forall ('a : Type). register('a) -> 'a effect {rreg}

//             EL1 physical        EL2 physical        EL3 physical        EL1 virtual,       EL2 virtual
let CNT_CVAL = [ref CNTP_CVAL_EL0, ref CNTHP_CVAL_EL2, ref CNTPS_CVAL_EL1, ref CNTV_CVAL_EL0, ref CNTHV_CVAL_EL2]
let CNT_TVAL = [ref CNTP_TVAL_EL0, ref CNTHP_TVAL_EL2, ref CNTPS_TVAL_EL1, ref CNTV_TVAL_EL0, ref CNTHV_TVAL_EL2]
let CNT_CTL  = [ref CNTP_CTL_EL0,  ref CNTHP_CTL_EL2,  ref CNTPS_CTL_EL1,  ref CNTV_CTL_EL0,  ref CNTHV_CTL_EL2 ]
let CNT_CTL  = [ref CNTP_CTL_EL0,  ref CNTHP_CTL_EL2,  ref CNTPS_CTL_EL1,  ref CNTV_CTL_EL0,  ref CNTHV_CTL_EL2 ]
let CNT_IRQ  = [0x0000_000d,       0x0000_000a,        0x0000_03ff,        0x0000_000b,       0x0000_03ff       ]
//                                                     No IRQ                                 No IRQ?

// SGI Interrupts are 0-15, PPI interrupts are 16-31, so SPI interrupts have an offset of 32.
let SPI_OFFSET = 32

val get_cycle_count = { c: "get_cycle_count" } : unit -> int effect {escape, undef, wreg, rreg, rmem, wmem}

// Advance CPU by one cycle
val Step_CPU : unit -> unit effect {escape, undef, wreg, rreg, rmem, wmem}

function Step_CPU() = {
  // Check for pending interrupts
  var interrupt_req : InterruptReq = undefined;
  interrupt_req.take_SE  = true; interrupt_req.take_vSE  = true;
  interrupt_req.take_IRQ = true; interrupt_req.take_vIRQ = true;
  interrupt_req.take_FIQ = true; interrupt_req.take_vFIQ = true;
  try {
      var interrupted = false;
      interrupted = TakePendingInterrupts(interrupt_req);
      if interrupted then {
          print("Pending interrupt taken\n");
      }
  } catch {
      _ => {
        print("Unhandled exception while pending exceptions\n");
      }
  };

  var fetch_ok = false;
  try {
      __currentInstr       = __fetchA64();
      __currentInstrLength = 4;
      fetch_ok = true;
  } catch {
      Error_ExceptionTaken() => {
        print(concat_str("Exception taken during IFetch from PC=", concat_str(HexStr(UInt(aget_PC())), concat_str(" in cycle=", concat_str(DecStr(get_cycle_count()), "\n")))));
      },
      _ => {
        print("Exiting due to unhandled exception during fetch\n");
        exit()
      }
  };

  if fetch_ok then {
      try {
          __PC_changed = false;
          ShouldAdvanceIT = (PSTATE.nRW == [bitone]) & (PSTATE.T == [bitone]);
          decode(__currentInstr);
      } catch {
          // note: if supporting AArch32 as well, call _UndefinedFault() instead
          Error_Undefined()         => try { AArch64_UndefinedFault() } catch { _ => print("Exception during Undefined recovery\n") },
          Error_See(_)              => try { AArch64_UndefinedFault() } catch { _ => print("Exception during SEE recovery\n") },
          Error_ReservedEncoding(_) => try { AArch64_UndefinedFault() } catch { _ => print("Exception during ReservedEncoding recovery\n") },
          Error_ExceptionTaken() => {
            print(concat_str("ExceptionTaken during Decode/Execute from PC=", concat_str(HexStr(UInt(aget_PC())), concat_str(" opcode=", concat_str(HexStr(UInt(__currentInstr)), concat_str(" in cycle ", concat_str(DecStr(get_cycle_count()), "\n")))))));
            // print("  This might just be a HINT like 0xd50320df\n");
            ()
          },
          Error_Implementation_Defined(s) => {
            print(concat_str("IMPLEMENTATION_DEFINED ", concat_str(s, "\n")));
            exit();
          }
      }
  };
  if ~(__PC_changed) then _PC = _PC + __currentInstrLength else ();
  if ShouldAdvanceIT then AArch32_ITAdvance() else ();
  SSAdvance();
  __UpdateSystemCounter(); // should this happen even if sleeping?
}

// Advance Timers by one cycle
val Step_Timers : unit -> unit effect {escape, undef, wreg, rreg, rmem, wmem}

function Step_Timers() = {
  // Increment the counter
  CNTPCT_EL0 = CNTPCT_EL0 + 1;
  CNTVCT_EL0 = CNTPCT_EL0 - CNTVOFF_EL2;

  // Timer value view for each timer
  foreach (timer from 0 to 4) {
    let TVAL = CNT_TVAL[timer];
    let nextTVAL = read_register(TVAL) - 1;
    (*TVAL) = nextTVAL;

    if nextTVAL == 0x0000_0000 then {
      _IRQPending = true;
      AArch64_TakePhysicalIRQException()
    }
  };

  // Handle the Kernel event stream, if enabled by CNTKCTL_EL1[2].
  if CNTKCTL_EL1[2] == bitone then {
    let mask = LSL(ZeroExtend(0x1, 64), UInt(CNTKCTL_EL1[7 .. 4]));

    // Trigger event stream on either rising bit (0-1, bitzero) or falling (1-0, bitone)
    let trigger : bool = if CNTKCTL_EL1[3] == bitzero then {
      ((CNTVCT_EL0 - 1) & mask) == Zeros() & (CNTVCT_EL0 & mask) != Zeros()
    } else {
      ((CNTVCT_EL0 - 1) & mask) != Zeros() & (CNTVCT_EL0 & mask) == Zeros()
    };

    if trigger & PSTATE.I == bitzero then {
      _IRQPending = true;
      AArch64_TakePhysicalIRQException()
    }
  };

  // Handle the Hypervisor event stream, if enabled by CNTHCTL_EL2[2].
  if CNTHCTL_EL2[2] == bitone then {
    let mask = LSL(ZeroExtend(0x1, 64), UInt(CNTHCTL_EL2[7 .. 4]));

    // Trigger event stream on either rising bit (0-1, bitzero) or falling (1-0, bitone)
    let trigger : bool = if CNTHCTL_EL2[3] == bitzero then {
      ((CNTPCT_EL0 - 1) & mask) == Zeros() & (CNTPCT_EL0 & mask) != Zeros()
    } else {
      ((CNTPCT_EL0 - 1) & mask) != Zeros() & (CNTPCT_EL0 & mask) == Zeros()
    };

    if trigger & PSTATE.I == bitzero then {
      prerr("[Clock] Tick\n");
      _IRQPending = true;
      AArch64_TakePhysicalIRQException()
    }
  }
}

// Simple top level fetch and execute loop.
val fetch_and_execute : unit -> unit effect {escape, undef, wreg, rreg, rmem, wmem}

function fetch_and_execute () = {
    try {
      Step_Timers();

      var prevEL = PSTATE.EL;
      var prevI = PSTATE.I;

      // Store the old values of the Counter-timer Kernel/Hypervisor Control
      // registers, as we want to figure out when they changes.
      var prevCNTKCTL_EL1 = CNTKCTL_EL1;
      var prevCNTHCTL_EL2 = CNTHCTL_EL2;

      if ~(__Sleeping()) then {
          Step_CPU();
      };

      // We want to keep track of what exception level we are in for debugging purposes.
      if UInt(prevEL) > UInt(PSTATE.EL) then {
        prerr_bits("[Sail] Exception level dropped to: ", PSTATE.EL)
      };
      if prevI != PSTATE.I then {
	prerr_bits("[Sail] PSTATE.I changed to: ", PSTATE.I);
        print(concat_str("   at PC=", concat_str(HexStr(UInt(aget_PC())), concat_str(" in cycle=", concat_str(DecStr(get_cycle_count()), "\n")))));
      };
      if prevCNTKCTL_EL1 != CNTKCTL_EL1 then {
        prerr_bits("[Clock] CNTKCTL_EL1 changed to ", CNTKCTL_EL1);
      };
      if prevCNTHCTL_EL2 != CNTHCTL_EL2 then {
        prerr_bits("[Clock] CNTHCTL_EL2 changed to ", CNTHCTL_EL2);
      }

    } catch {
      Error_See(str) if str == "HINT" => (),
      Error_ExceptionTaken(_) => {
	// enable_tracing()
        ()
      },
      _ => {
        prerr("Exiting due to unhandled exception\n");
        exit()
      }
    };
    __EndCycle(); // advance state of non-sleeping parts of the system
}

let COLD_RESET : bool = true

val "load_raw" : (bits(64), string) -> unit

val init : unit -> unit effect {escape, undef, rreg, wreg}

function init() = {
  __currentInstrLength = 4;
  TakeReset(COLD_RESET);
}

val main : unit -> unit effect {escape, undef, wreg, rreg, rmem, wmem}

val check_cycle_count = { c: "cycle_count" } : unit -> unit

function main() = {
  init();
  while true do {
    fetch_and_execute();
    check_cycle_count();
  }
}