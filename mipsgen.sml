signature CODEGEN =
sig
  structure F: FRAME
  val codegen: Frame.frame -> Tree.stm -> Assem.instr list
end

structure MipsGen : CODEGEN =
struct
  structure F = MipsFrame
  structure A = Assem
  structure T = Tree
  structure S = Symbol
  structure E = ErrorMsg

  fun codegen (frame) (stm: Tree.stm) : A.instr list =
    let
      val ilist = ref (nil: A.instr list)
      fun emit x = ilist := x::(!ilist)
      fun result(gen) = let val t = Temp.newtemp() in gen t; t end

      fun mipsIntToString i = if i >= 0 then Int.toString i else "-" ^ Int.toString (Int.abs i)

      fun munchStm (T.SEQ(lst)) = (case lst of
                                      []   => ()
                                    | a::l => (munchStm(a); munchStm(Tree.SEQ(l))))
        | munchStm (T.CJUMP(relop, e1, e2, label1, label2)) =
            (case relop of
                T.EQ => emit (A.OPER{assem = "beq $`s0, $`s1, " ^ (S.name label1) ^ "\n",
                                      src = [munchExp e1, munchExp e2],
                                      dst = [],
                                      jump = SOME [label1, label2]})
              | T.NE => emit (A.OPER{assem = "bne $`s0, $`s1, " ^ (S.name label1) ^ "\n",
                                      src = [munchExp e1, munchExp e2],
                                      dst = [],
                                      jump = SOME [label1, label2]})
              | T.LT => emit (A.OPER{assem = "blt $`s0, $`s1, " ^ (S.name label1) ^ "\n",
                                      src = [munchExp e1, munchExp e2],
                                      dst = [],
                                      jump = SOME [label1, label2]})
              | T.GT => emit (A.OPER{assem = "bgt $`s0, $`s1, " ^ (S.name label1) ^ "\n",
                                      src = [munchExp e1, munchExp e2],
                                      dst = [],
                                      jump = SOME [label1, label2]})
              | T.LE => emit (A.OPER{assem = "ble $`s0, $`s1, " ^ (S.name label1) ^ "\n",
                                      src = [munchExp e1, munchExp e2],
                                      dst = [],
                                      jump = SOME [label1, label2]})
              | T.GE => emit (A.OPER{assem = "bge $`s0, $`s1, " ^ (S.name label1) ^ "\n",
                                      src = [munchExp e1, munchExp e2],
                                      dst = [],
                                      jump = SOME [label1, label2]})
              | T.ULT => emit (A.OPER{assem = "bltu $`s0, $`s1, " ^ (S.name label1) ^ "\n",
                                      src = [munchExp e1, munchExp e2],
                                      dst = [],
                                      jump = SOME [label1, label2]})
              | T.UGT => emit (A.OPER{assem = "bgtu $`s0, $`s1, " ^ (S.name label1) ^ "\n",
                                      src = [munchExp e1, munchExp e2],
                                      dst = [],
                                      jump = SOME [label1, label2]})
              | T.ULE => emit (A.OPER{assem = "bleu $`s0, $`s1, " ^ (S.name label1) ^ "\n",
                                      src = [munchExp e1, munchExp e2],
                                      dst = [],
                                      jump = SOME [label1, label2]})
              | T.UGE => emit (A.OPER{assem = "bgeu $`s0, $`s1, " ^ (S.name label1) ^ "\n",
                                      src = [munchExp e1, munchExp e2],
                                      dst = [],
                                      jump = SOME [label1, label2]}))

        (*store word operations: first expression is T.MEM, second expression is what we load there*)
        | munchStm (T.MOVE(T.MEM(T.BINOP(T.PLUS, e1, T.CONST i)), e2)) =
            emit (A.OPER {assem = "sw $`s0, " ^ mipsIntToString i ^ "($`s1)\n",
                          src = [munchExp e2, munchExp e1],
                          dst = [],
                          jump = NONE})

        | munchStm (T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, e1)), e2)) =
            emit (A.OPER {assem = "sw $`s0, " ^ mipsIntToString i ^ "($`s1)\n",
                          src = [munchExp e2, munchExp e1],
                          dst = [],
                          jump = NONE})

        | munchStm (T.MOVE(T.MEM(T.BINOP(T.MINUS, e1, T.CONST i)), e2)) =
            emit (A.OPER {assem = "sw $`s0, " ^ mipsIntToString (~i) ^ "($`s1)\n",
                          src = [munchExp e2, munchExp e1],
                          dst = [],
                          jump = NONE})

        | munchStm (T.MOVE(T.MEM(T.CONST i), e2)) =
            emit (A.OPER {assem = "sw $`s0,  " ^ mipsIntToString i ^ "($`s1)\n",
                          src = [munchExp e2, F.R0],
                          dst = [],
                          jump = NONE})

        | munchStm (T.MOVE(T.MEM(e1), e2)) =
            emit (A.OPER {assem = "sw $`s0,  0($`s1)\n",
                          src = [munchExp e2, munchExp e1],
                          dst = [],
                          jump = NONE})

        (*load word operations: first expression is what we load into the T.MEM of the second expression*)
        | munchStm (T.MOVE(e1, T.MEM(T.BINOP(T.PLUS, e2, T.CONST i)))) =
            emit (A.OPER {assem = "lw $`d0, " ^ mipsIntToString i ^  "($`s0)\n",
                          src = [munchExp e2],
                          dst = [munchExp e1],
                          jump = NONE})

        | munchStm (T.MOVE(e1, T.MEM(T.BINOP(T.PLUS, T.CONST i, e2)))) =
            emit (A.OPER {assem = "lw $`d0, " ^ mipsIntToString i ^  "($`s0)\n",
                          src = [munchExp e2],
                          dst = [munchExp e1],
                          jump = NONE})

        | munchStm (T.MOVE(e1, T.MEM(T.BINOP(T.MINUS, e2, T.CONST i)))) =
            emit (A.OPER {assem = "lw $`d0, " ^ mipsIntToString (~i) ^  "($`s0)\n",
                          src = [munchExp e2],
                          dst = [munchExp e1],
                          jump = NONE})

        | munchStm (T.MOVE(e1, T.MEM(T.CONST i))) =
            emit (A.OPER {assem = "lw $`d0, " ^ mipsIntToString i ^  "($`s0)\n",
                          src = [F.R0],
                          dst = [munchExp e1],
                          jump = NONE})

        | munchStm (T.MOVE(e1, T.MEM(e2))) =
            emit (A.OPER {assem = "lw $`d0, 0($`s0)\n",
                          src = [munchExp e2],
                          dst = [munchExp e1],
                          jump = NONE})

        (* moving something from one register into another*)
        | munchStm (T.MOVE(e1, T.CONST i)) =
            emit (A.OPER {assem = "li $`d0, " ^ mipsIntToString i ^ "\n",
                          src = [],
                          dst = [munchExp e1],
                          jump = NONE})

        | munchStm (T.MOVE(e1, T.NAME l)) =
            emit (A.OPER {assem = "la $`d0, " ^ (S.name l) ^ "\n",
                          src = [],
                          dst = [munchExp e1],
                          jump = NONE})

        | munchStm (T.MOVE(e1, e2)) =
             emit (A.MOVE {assem = "move $`d0,  $`s0\n",
                           src = munchExp e2,
                           dst = munchExp e1})

        | munchStm (T.JUMP(T.NAME label, label_list)) =
            emit (A.OPER {assem = "j " ^ (S.name label) ^ "\n",
                          src = [],
                          dst = [],
                          jump = SOME(label_list)})

        | munchStm (T.JUMP(exp, label_list)) =
            emit (A.OPER {assem = "jr $`j0\n",
                          src = [munchExp exp],
                          dst = [],
                          jump = SOME(label_list)})

        | munchStm (T.EXP(e)) = (munchExp e; ())

        | munchStm (T.LABEL lab) = emit (A.LABEL({assem = (S.name lab) ^ ":\n", lab = lab}))

      and munchExp (T.TEMP t) = t
        | munchExp (T.CONST i) =
              result (fn r => emit(A.OPER
                {assem="addi $`d0, $`s0, " ^ mipsIntToString i ^ "\n",
                 src=[F.R0], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.PLUS, T.CONST i, e)) =
              result (fn r => emit(A.OPER
                {assem="addi $`d0, $`s0, " ^ mipsIntToString i ^ "\n",
                 src=[munchExp e], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.PLUS, e, T.CONST i)) =
              result (fn r => emit(A.OPER
                {assem="addi $`d0, $`s0, " ^ mipsIntToString i ^ "\n",
                 src=[munchExp e], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.PLUS, e1, e2)) =
              result (fn r => emit(A.OPER
                {assem="add $`d0, $`s0, $`s1\n",
                 src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.MINUS, e, T.CONST i)) =
              result (fn r => emit(A.OPER
                {assem="addi $`d0, $`s0, " ^ mipsIntToString (~i) ^ "\n",
                 src=[munchExp e], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.MINUS, e1, e2)) =
              result (fn r => emit(A.OPER
                {assem="sub $`d0, $`s0, $`s1\n",
                 src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.MUL, e1, e2)) =
              result (fn r => emit(A.OPER
                {assem="mul $`d0, $`s0, $`s1\n",
                 src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.DIV, e1, e2)) =
              result (fn r => emit(A.OPER
                {assem="div $`d0, $`s0, $`s1\n",
                 src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.OR, T.CONST i, e)) =
              result (fn r => emit(A.OPER
                {assem="ori $`d0, $`s0, " ^ mipsIntToString i ^ "\n",
                 src=[munchExp e], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.OR, e, T.CONST i)) =
              result (fn r => emit(A.OPER
                {assem="ori $`d0, $`s0, " ^ mipsIntToString i ^ "\n",
                 src=[munchExp e], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.OR, e1, e2)) =
              result (fn r => emit(A.OPER
                {assem="or $`d0, $`s0, $`s1\n",
                 src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.AND, T.CONST i, e)) =
              result (fn r => emit(A.OPER
                {assem="andi $`d0, $`s0, " ^ mipsIntToString i ^ "\n",
                 src=[munchExp e], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.AND, e, T.CONST i)) =
              result (fn r => emit(A.OPER
                {assem="andi $`d0, $`s0, " ^ mipsIntToString i ^ "\n",
                 src=[munchExp e], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.AND, e1, e2)) =
              result (fn r => emit(A.OPER
                {assem="and $`d0, $`s0, $`s1\n",
                 src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.XOR, T.CONST i, e)) =
              result (fn r => emit(A.OPER
                {assem="xori $`d0, $`s0, " ^ mipsIntToString i ^ "\n",
                 src=[munchExp e], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.XOR, e, T.CONST i)) =
              result (fn r => emit(A.OPER
                {assem="xori $`d0, $`s0, " ^ mipsIntToString i ^ "\n",
                 src=[munchExp e], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.XOR, e1, e2)) =
              result (fn r => emit(A.OPER
                {assem="xor $`d0, $`s0, $`s1\n",
                 src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.LSHIFT, e, T.CONST i)) =
              result (fn r => emit(A.OPER
                {assem="sll $`d0, $`s0, " ^ mipsIntToString i ^ "\n",
                 src=[munchExp e], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.LSHIFT, e1, e2)) =
              result (fn r => emit(A.OPER
                {assem="sllv $`d0, $`s0, $`s1\n",
                 src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.RSHIFT, e, T.CONST i)) =
              result (fn r => emit(A.OPER
                {assem="srl $`d0, $`s0, " ^ mipsIntToString i ^ "\n",
                 src=[munchExp e], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.RSHIFT, e1, e2)) =
              result (fn r => emit(A.OPER
                {assem="srlv $`d0, $`s0, $`s1\n",
                 src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.ARSHIFT, e, T.CONST i)) =
              result (fn r => emit(A.OPER
                {assem="sra $`d0, $`s0, " ^ mipsIntToString i ^ "\n",
                 src=[munchExp e], dst=[r], jump=NONE}))

        | munchExp (T.BINOP(T.ARSHIFT, e1, e2)) =
              result (fn r => emit(A.OPER
                {assem="srav $`d0, $`s0, $`s1\n",
                 src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

        | munchExp (T.MEM(T.BINOP(T.PLUS, e, T.CONST i))) =
              result (fn r => emit(A.OPER
                {assem="lw $`d0, " ^ mipsIntToString i ^ "($`s0)\n",
                 src=[munchExp e], dst=[r], jump=NONE}))

        | munchExp (T.MEM(T.BINOP(T.PLUS, T.CONST i, e))) =
              result (fn r => emit(A.OPER
                {assem="lw $`d0, " ^ mipsIntToString i ^ "($`s0)\n",
                 src=[munchExp e], dst=[r], jump=NONE}))

        | munchExp (T.MEM(T.BINOP(T.MINUS, e, T.CONST i))) =
              result (fn r => emit(A.OPER
                {assem="lw $`d0, " ^ mipsIntToString (~i) ^ "($`s0)\n",
                 src=[munchExp e], dst=[r], jump=NONE}))

        | munchExp (T.MEM(T.CONST(i))) =
              result (fn r => emit (A.OPER
                {assem = "lw $`d0, " ^ mipsIntToString (i) ^ "($`s0)",
                 src = [F.R0], dst = [r], jump = NONE}))

        | munchExp (T.MEM(e)) =
              result (fn r => emit(A.OPER
                {assem="lw $`d0, 0($`s0)\n",
                 src=[munchExp e], dst=[r], jump=NONE}))

        | munchExp (T.ESEQ(s,e)) = (munchStm s; munchExp e)

        | munchExp (T.NAME(l)) =
              result (fn r => emit(A.OPER
                {assem="la $`d0, " ^ S.name l ^ "\n",
                 src=[], dst=[r], jump=NONE}))

        | munchExp (T.CALL(T.NAME(l), args)) =
              let
                val calldefs = F.RV::F.RA::F.FP::F.get_registers F.callersaves
                val num_args = List.length args
                val sp_offset = if num_args < 4
                                then 0
                                else F.wordSize * (num_args - 4)
              in
                (emit(A.OPER
                    {assem="jal " ^ S.name l ^ "\n",
                     src=munchArgs(0, args, 0, ref 0), dst=F.RA::F.RV::F.get_registers F.callersaves, jump=SOME([l])});
                 if sp_offset > 0
                 then munchStm(Tree.MOVE(Tree.TEMP F.SP, Tree.BINOP(Tree.PLUS, Tree.TEMP F.SP, Tree.CONST sp_offset)))
                 else ();
                 F.RV)
              end

        | munchExp (_) = (E.error 0 "Intermediate Representation Tree tile could not be translated (exp)."; Temp.newtemp())

      and munchArgs(ind, [], regs_used, sp_offset) = (if !sp_offset > 0
                                                      then munchStm(Tree.MOVE(Tree.TEMP F.SP, Tree.BINOP(Tree.MINUS, Tree.TEMP F.SP, Tree.CONST (!sp_offset))))
                                                      else ();
                                                      [])
        | munchArgs(ind, a::l, regs_used, sp_offset) =
              let
                fun moveArgToReg arg =
                        munchStm(T.MOVE(T.TEMP (List.nth (F.get_registers F.argregs, regs_used)), arg))
                fun moveArgToFrame arg = (sp_offset := !sp_offset + F.wordSize;
                        munchStm(T.MOVE(T.MEM(T.BINOP(T.MINUS, T.TEMP(F.SP), T.CONST (!sp_offset - F.wordSize) )), arg)))
              in
                if regs_used < 4
                then (moveArgToReg a; List.nth (F.get_registers F.argregs, regs_used)::munchArgs(ind + 1, l, regs_used+1, sp_offset))
                else (moveArgToFrame a; Temp.newtemp()::munchArgs(ind + 1, l, regs_used, sp_offset))
              end

    in
      munchStm stm;
      rev(!ilist)
    end
end
