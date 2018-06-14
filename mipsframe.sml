structure MipsFrame : FRAME =
struct
  datatype access = InFrame of int | InReg of Temp.temp
  type frame = {name: Temp.label, formals: access list, numVars: int ref, sp:  int ref}
  datatype frag = PROC of {body:Tree.stm, frame:frame}
                | STRING of Temp.label * string

  type register = string

  val wordSize = 4;

  structure E = ErrorMsg

  (* Registers *)
  val R0 = Temp.newtemp() (* 100 *)
  val AT = Temp.newtemp() (* 101 *)
  val RV = Temp.newtemp() (* 102 *)
  val V1 = Temp.newtemp() (* 103 *)
  val A0 = Temp.newtemp() (* 104 *)
  val A1 = Temp.newtemp() (* 105 *)
  val A2 = Temp.newtemp() (* 106 *)
  val A3 = Temp.newtemp() (* 107 *)
  val T0 = Temp.newtemp() (* 108 *)
  val T1 = Temp.newtemp() (* 109 *)
  val T2 = Temp.newtemp() (* 110 *)
  val T3 = Temp.newtemp() (* 111 *)
  val T4 = Temp.newtemp() (* 112 *)
  val T5 = Temp.newtemp() (* 113 *)
  val T6 = Temp.newtemp() (* 114 *)
  val T7 = Temp.newtemp() (* 115 *)
  val S0 = Temp.newtemp() (* 116 *)
  val S1 = Temp.newtemp() (* 117 *)
  val S2 = Temp.newtemp() (* 118 *)
  val S3 = Temp.newtemp() (* 119 *)
  val S4 = Temp.newtemp() (* 120 *)
  val S5 = Temp.newtemp() (* 121 *)
  val S6 = Temp.newtemp() (* 122 *)
  val S7 = Temp.newtemp() (* 123 *)
  val T8 = Temp.newtemp() (* 124 *)
  val T9 = Temp.newtemp() (* 125 *)
  val K0 = Temp.newtemp() (* 126 *)
  val K1 = Temp.newtemp() (* 127 *)
  val GP = Temp.newtemp() (* 128 *)
  val SP = Temp.newtemp() (* 129 *)
  val FP = Temp.newtemp() (* 130 *)
  val RA = Temp.newtemp() (* 131 *)

  (* Register lists *)
  val zeroreg = (R0, "0")
  val usablespecialregs = [(AT, "at"),
                           (RV, "v0"),
                           (V1, "v1"),
                           (K0, "k0"),
                           (K1, "k1"),
                           (GP, "gp"),
                           (SP, "sp"),
                           (FP, "s8"),
                           (RA, "ra")]
  val specialregs = zeroreg :: usablespecialregs
  val argregs = [(A0, "a0"),
                 (A1, "a1"),
                 (A2, "a2"),
                 (A3, "a3")]
  val calleesaves = [(S0, "s0"),
                     (S1, "s1"),
                     (S2, "s2"),
                     (S3, "s3"),
                     (S4, "s4"),
                     (S5, "s5"),
                     (S6, "s6"),
                     (S7, "s7")]
  val callersaves = [(T0, "t0"),
                     (T1, "t1"),
                     (T2, "t2"),
                     (T3, "t3"),
                     (T4, "t4"),
                     (T5, "t5"),
                     (T6, "t6"),
                     (T7, "t7"),
                     (T8, "t8"),
                     (T9, "t9")]

  fun get_registers typeregs = map (fn (reg, str) => reg) typeregs (* TODO: Change function name? *)

  val registers = map (fn(reg, str) => str) (callersaves @ calleesaves @ argregs @ usablespecialregs)

  fun getStackPointer {name = _, formals = _, numVars = _, sp = offset} = !offset
  fun moveStackPointerDown {name = _, formals = _, numVars = _, sp = offset} = offset := !offset + wordSize
  fun incrementVars {name = _, formals = _, numVars = locals, sp = _} = locals := !locals + 1

  fun printAccesses [] = (print("End of AccessList\n"))
    | printAccesses (a::l) = case a of
                            InFrame offset => (print ("InFrame " ^ Int.toString offset ^ "\n"); printAccesses(l))
                            |  InReg temp => (print ("InReg " ^ Temp.makestring temp ^ "\n"); printAccesses(l))

  fun newFrame {name:Temp.label, formals: bool list} =
    let
      val escape_count = ref 0
      fun createFormalsList ([], offset, registersUsed, index) = []

        | createFormalsList (current::l, offset, registersUsed, 0) =
              (escape_count := !escape_count+1; InFrame(offset)::createFormalsList(l, offset - (1 + List.length calleesaves)*wordSize, registersUsed, 1))

        | createFormalsList (current::l, offset, registersUsed, index) =
              if current then (escape_count := !escape_count+1; InFrame(offset)::createFormalsList(l, offset - wordSize, registersUsed, index+1) )
              else (if registersUsed >= 4
                   then (escape_count := !escape_count+1; InFrame(offset)::createFormalsList(l, offset - wordSize, registersUsed, index+1))
                   else InReg(Temp.newtemp())::createFormalsList(l, offset, registersUsed + 1, index+1))

      val formals' = createFormalsList(formals, 0, 0, 0)
      val sp_offset = !escape_count*wordSize + (List.length calleesaves)*wordSize + 2*wordSize
   in
      {name = name, formals = formals', numVars = ref 0, sp = ref sp_offset}
   end

  fun name {name = name', formals = _, numVars = _, sp = _} = name'

  fun formals {name = _, formals = formals', numVars = _, sp = _} = formals'

  fun allocLocal frame escapes =
    if escapes then ((incrementVars frame; moveStackPointerDown frame; InFrame((getStackPointer frame)-wordSize)))
    else (incrementVars frame; InReg(Temp.newtemp()))

  fun externalCall (s, args) = Tree.CALL(Tree.NAME(Temp.namedlabel s), args)

  fun exp (InFrame offset) frpointer = (Tree.MEM(Tree.BINOP(Tree.MINUS, frpointer, Tree.CONST offset)))
        | exp (InReg register) frpointer = Tree.TEMP(register)

  fun procEntryExit1 (frame as {name=name, formals=formals, numVars, sp=sp}, body) =
           let
              val offset = ref wordSize
              fun saveCalleeReg (reg) = (offset := !offset - wordSize;
                                         Tree.MOVE(Tree.MEM(Tree.BINOP(Tree.PLUS, Tree.TEMP SP,Tree.CONST (!offset))), Tree.TEMP reg))
              fun moveArgs([], seq, arg_no) = seq
                | moveArgs(a::l, seq, arg_no) =
                      if arg_no < 4
                      then
                          case a of
                            InFrame fp_offset => ((*moveStackPointerDown(frame); *) offset := !offset - wordSize;
                                               Tree.MOVE(Tree.MEM(Tree.BINOP(Tree.PLUS, Tree.TEMP SP, Tree.CONST (fp_offset))),
                                                         Tree.TEMP (List.nth (get_registers argregs, arg_no)))::moveArgs(l, seq, arg_no+1))
                          | InReg temp => Tree.MOVE(Tree.TEMP temp,
                                                    Tree.TEMP (List.nth (get_registers argregs, arg_no)))::moveArgs(l, seq, arg_no+1)
                      else
                          case a of
                            InFrame fp_offset => ((*moveStackPointerDown(frame);*) offset := !offset + wordSize;
                                               Tree.MOVE(Tree.MEM(Tree.BINOP(Tree.PLUS, Tree.TEMP SP, Tree.CONST (fp_offset))),
                                                         Tree.MEM(Tree.BINOP(Tree.PLUS, Tree.TEMP SP, Tree.CONST ((arg_no-4)*wordSize))))::moveArgs(l, seq, arg_no+1))
                          | InReg temp => Tree.MOVE(Tree.TEMP temp,
                                                    Tree.MEM(Tree.BINOP(Tree.PLUS, Tree.TEMP SP, Tree.CONST ((arg_no-4)*wordSize))))::moveArgs(l, seq, arg_no+1)
              val sl::args = formals
              val saveSL = case sl of
                            InFrame fp_offset => (offset := !offset - wordSize;
                                                    Tree.MOVE(Tree.MEM(Tree.BINOP(Tree.PLUS, Tree.TEMP SP, Tree.CONST (fp_offset))),
                                                     Tree.TEMP (List.nth (get_registers argregs, 0))))
                            |  _              => (E.error 0 "Static Link must be saved InFrame"; Tree.EXP( Tree.CONST 0))

              val saveRA = (offset := !offset - wordSize;
                            Tree.MOVE(Tree.MEM(Tree.BINOP(Tree.PLUS, Tree.TEMP SP, Tree.CONST (!offset))), Tree.TEMP RA))
              val ra_offset = !offset
              val saveFP = (offset := !offset - wordSize;
                            Tree.MOVE(Tree.MEM(Tree.BINOP(Tree.PLUS, Tree.TEMP SP,Tree.CONST (!offset))), Tree.TEMP FP))
              val fp_offset = !offset
              val saveCalleeStms = map saveCalleeReg (get_registers calleesaves)
              val moveArgsStms = moveArgs(args, [], 1)
              val moveFP = Tree.MOVE(Tree.TEMP FP, Tree.TEMP SP)
              val moveSP = Tree.MOVE(Tree.TEMP SP, Tree.BINOP(Tree.MINUS, Tree.TEMP SP, Tree.CONST (!sp)))
            in
              (* Tree.SEQ([Tree.LABEL(name)] @ moveArgsStms @ saveCalleeStms @ [saveRA] @ [moveSP] @ [body]) *)
              (* Funtion Call Debug*)
              (*(Tree.ESEQ(Tree.SEQ([Tree.LABEL(name)] @ moveArgsStms),
                        body), ra_offset, fp_offset, sp) *)
              (Tree.ESEQ(Tree.SEQ([Tree.LABEL(name)] @ [saveSL] @ [saveRA] @ [saveFP] @ saveCalleeStms @ moveArgsStms @ [moveFP] @ [moveSP] ),
                        body),
               ra_offset, fp_offset, !sp)
            end

  fun procEntryExit2 body =
            body @ [Assem.OPER{assem = "", src = [AT, K0, K1, GP, R0, RV, RA, FP, SP], dst = [], jump = NONE},
                    Assem.OPER{assem = "jr $`s0 \n", src = [RA], dst = [], jump = SOME([])}]

  fun procEntryExit2' body =
            body @ [Assem.OPER{assem = " ", src = [AT, K0, K1, GP, R0, RV, RA, FP, SP], dst = [], jump = NONE}]
            (*body @ [Assem.OPER{assem = " ", src = [AT, K0, K1, GP, R0, RV, RA, FP, SP]@(get_registers calleesaves), dst = [], jump = NONE}] *)

  fun procEntryExit3 ({name=name, formals, numVars, sp}, body) =
            {prolog = "PROCEDURE " ^ Symbol.name name ^ "\n",
             body = body,
             epilog = "END " ^ Symbol.name name ^ "\n"}

  val tempMap =
        let
          fun add_regs ((reg, name), curr_map) = Temp.Table.enter(curr_map, reg, name)
          val allregs = specialregs @ argregs @ calleesaves @ callersaves
        in
          foldl add_regs Temp.Table.empty allregs
        end

  fun tempToString (temp) =
      case Temp.Table.look(tempMap, temp) of
          SOME(n) => n
        | NONE => Temp.makestring temp

  fun string (temp, s) = "Label: " ^ (Symbol.name temp) ^ ", String: " ^ s


end
