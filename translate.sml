structure Frame = MipsFrame

signature TRANSLATE =
sig
  type level
  type access (* not same as Frame.access *)
  type exp

  val outermost : level

	val newLevel : {parent: level, name: Temp.label, formals: bool list} -> level
  val formals : level -> access list
  val allocLocal : level -> bool -> access

  val unEx : exp -> Tree.exp
  val unNx : exp -> Tree.stm
  val unCx : exp -> (Temp.label * Temp.label -> Tree.stm)

  val translateSimpleVar : access * level -> exp
  val translateFieldVar : exp * int -> exp
  val translateSubscriptVar : exp * exp -> exp

  val translateInt : int -> exp (* done *)
  val translateString : string -> exp (* done *)
  val translateNil : unit -> exp (* done *)
  val translateSequence : exp list -> exp (* done *)
  val translateBinOp : Absyn.oper * exp * exp -> exp (* done *)
  val translateRelOp: Absyn.oper * exp * exp * bool -> exp (* done *)
  val translateIf : exp * exp * exp -> exp (* done *)
  val translateAssign : exp * exp -> exp (* done *)
  val translateWhile : exp * exp * Temp.label -> exp (* done *)
  val translateBreak : Temp.label -> exp (* done *)
  val translateFor : exp * bool ref * exp * exp * exp * Temp.label -> exp (* done *)
  val translateArray : exp * exp -> exp (* done *)
  val translateRecord : exp list -> exp
  val translateLet : exp list * exp -> exp (* done *)
  val translateCall: level * level * Temp.label * exp list -> exp
  val translateStdrdLbryCall: Symbol.symbol * exp list -> exp
	val resetFragList : unit -> unit

  val procEntryExit : {level: level, body:exp} -> unit
	val getResult : unit -> Frame.frag list

end


structure Translate : TRANSLATE =
struct

  datatype level =
       TOP
     | LEV of {unique: unit ref, parent: level, frame: Frame.frame}

  type access = level * Frame.access

	datatype exp = Ex of Tree.exp
							 | Nx of Tree.stm
							 | Cx of Temp.label * Temp.label -> Tree.stm

  val outermost = TOP
	val fragments = ref [] : Frame.frag list ref

  fun newLevel {parent, name, formals} =
    let
      val formals' = true::formals
    in
      LEV({unique=ref (), parent=parent, frame=Frame.newFrame{name=name, formals=formals'}})
    end

  fun allocLocal level escape =
    case level of
      LEV({unique=unique, parent=parent, frame=frame}) => (LEV({unique=unique, parent=parent, frame=frame}), Frame.allocLocal frame escape)
      | TOP => (ErrorMsg.error 0 "TOP Level has no frame"; (outermost, Frame.allocLocal (Frame.newFrame {name=Temp.newlabel(), formals=[]}) escape))


  fun formals TOP = []
    | formals (current as LEV{unique, parent, frame}) =
        let
          fun addAccess (access, l) = (current, access)::l
        in
          foldr addAccess [] (Frame.formals frame)
        end

	fun unEx (Ex e) = e
	  | unEx (Cx genstm) =
			let val r = Temp.newtemp()
					val t = Temp.newlabel() and f = Temp.newlabel()
			in Tree.ESEQ(Tree.SEQ[Tree.MOVE(Tree.TEMP r, Tree.CONST 1),
																genstm(t, f),
																Tree.LABEL f,
																Tree.MOVE(Tree.TEMP r, Tree.CONST 0),
																Tree.LABEL t],
															Tree.TEMP r)
		  end
		| unEx (Nx s) = Tree.ESEQ(s, Tree.CONST 0)

  fun unCx (Cx c) = c
    | unCx (Ex (Tree.CONST 0)) = (fn(t, f) => Tree.JUMP(Tree.NAME(f), [f]))
    | unCx (Ex (Tree.CONST 1)) = (fn(t, f) => Tree.JUMP(Tree.NAME(t), [t]))
    | unCx (Ex e) = (fn(t, f) => Tree.CJUMP(Tree.NE, e, Tree.CONST 0, t, f))
    | unCx (Nx _) = (ErrorMsg.error 0 "Conditional Expression Must Produce Value"; fn (a, b) => Tree.LABEL(Temp.newlabel()))

  fun unNx (Ex e) = Tree.EXP(e)
    | unNx (Nx n) = n
    | unNx (Cx c) = unNx(Ex(unEx(Cx c)))

  fun derefSLs TOP TOP currFP = (ErrorMsg.error 0 "Cannot access an outerscope. 1"; currFP)
    | derefSLs TOP currlevel currFP = (ErrorMsg.error 0 "Cannot access an outerscope. 2"; currFP)
    | derefSLs declevel TOP currFP = (ErrorMsg.error 0 "Cannot access an outerscope. 3"; currFP)
    | derefSLs (declevel as LEV{unique=decunique, parent=decparent, frame=decframe}) (currlevel as LEV{unique=currunique, parent=currparent, frame=currframe}) currFP =
        if decunique = currunique
        then currFP
        else derefSLs declevel currparent (Tree.MEM currFP) (* Keep dereferencing SL *)

        (* Tree.MOVE(unEx left, unEx right) *)

  fun translateCall (TOP, call_level, label, args) = Ex (Tree.TEMP Frame.FP)
    | translateCall (fun_level as LEV{unique, parent, frame as {name, formals=formals, numVars, sp}}, call_level, label, args) =
        let
          val sl = derefSLs parent call_level (Tree.TEMP Frame.FP)
          val args' = sl::(map unEx args)
          val args_access_list = formals
              (*  fun save_arg(arg, index) = Nx(Tree.Move(
                                              Frame.exp(List.nth(args_access_list, index))  (unEx arg)) *)
        in
          Ex(Tree.CALL(Tree.NAME label, args'))
        end

  fun translateStdrdLbryCall (func, args) =
        Ex(Frame.externalCall("tig_" ^ (Symbol.name func),
                              (map unEx args)))

  fun translateSimpleVar ((declevel, fraccess), currlevel) =
    Ex(Frame.exp (fraccess)(derefSLs declevel currlevel (Tree.TEMP Frame.FP)))

  fun translateFieldVar (var_exp, offset) =
      Ex(Tree.MEM(Tree.BINOP(
            Tree.PLUS, unEx var_exp,
            Tree.BINOP(Tree.MUL, Tree.CONST(offset), Tree.CONST(Frame.wordSize)))))

	fun translateInt num = Ex (Tree.CONST num)

  fun absynToTreeBinOp Absyn.PlusOp = Tree.PLUS
    | absynToTreeBinOp Absyn.MinusOp = Tree.MINUS
    | absynToTreeBinOp Absyn.TimesOp = Tree.MUL
    | absynToTreeBinOp Absyn.DivideOp = Tree.DIV
    | absynToTreeBinOp _ = ErrorMsg.impossible "Argument must be a binary operator"

  fun absynToTreeRelOp Absyn.EqOp = Tree.EQ
    | absynToTreeRelOp Absyn.NeqOp = Tree.NE
    | absynToTreeRelOp Absyn.LtOp = Tree.LT
    | absynToTreeRelOp Absyn.LeOp = Tree.LE
    | absynToTreeRelOp Absyn.GtOp = Tree.GT
    | absynToTreeRelOp Absyn.GeOp = Tree.GE
    | absynToTreeRelOp _ = ErrorMsg.impossible "Argument must be a relational operator"

	fun translateBinOp (binop, exp1, exp2) = Ex (Tree.BINOP(absynToTreeBinOp binop, unEx exp1, unEx exp2))

	fun translateRelOp (relop, exp1, exp2, false) = Cx (fn(t, f) => (Tree.CJUMP(absynToTreeRelOp relop, unEx exp1, unEx exp2, t, f)))
    | translateRelOp (relop, exp1, exp2, true) = Ex (Frame.externalCall("tig_stringEqual", [unEx exp1, unEx exp2]))

	fun translateIf (conditional, ifTrue, ifFalse) =
		let val condFn = unCx conditional
				val thenExp = unEx ifTrue
				val elseExp = unEx ifFalse
				val r = Temp.newtemp()
				val t = Temp.newlabel()
				val f = Temp.newlabel()
				val finish = Temp.newlabel()
		in
			Ex (Tree.ESEQ(Tree.SEQ[condFn(t, f),
														 Tree.LABEL f,
														 Tree.MOVE(Tree.TEMP r, elseExp),
														 Tree.JUMP(Tree.NAME(finish), [finish]),
                             Tree.LABEL t,
														 Tree.MOVE(Tree.TEMP r, thenExp),
														 Tree.JUMP(Tree.NAME(finish), [finish]),
														 Tree.LABEL finish],
														 Tree.TEMP r))
		end

  fun translateAssign (left, right) =
      Nx(Tree.MOVE(unEx left, unEx right))

	fun translateNil () = Ex (Tree.CONST 0)

	fun translateWhile (condition, body, false_label) =
		let
			val condFn = unCx condition
			val start = Temp.newlabel()
			val bodyNx = unNx body
			val t = Temp.newlabel()
      val cont = Temp.newlabel()
		in
			Nx (Tree.SEQ[Tree.LABEL start,
				 					 condFn (t, false_label),
                   Tree.LABEL false_label,
                   Tree.JUMP(Tree.NAME cont, [cont]),
									 Tree.LABEL t,
									 bodyNx,
									 Tree.JUMP(Tree.NAME start, [start]),
									 Tree.LABEL cont])
	 	end

	fun translateBreak (breaklabel) = Nx (Tree.JUMP(Tree.NAME(breaklabel), [breaklabel]))

	fun translateFor (iterator, escape, low, high, body, false_label) =
  		let
    			val variable = unEx iterator
    			val r = Temp.newtemp()
          val h = Temp.newtemp()
    			val init = unEx low
    			val limit = unEx high
    			val bodyNx = unNx body
    			val start = Temp.newlabel()
    			val t = Temp.newlabel()
          val cont = Temp.newlabel()
          val false_label' = Temp.newlabel()
  		in
    			Nx (Tree.SEQ[Tree.MOVE(Tree.TEMP r, init),
                       Tree.MOVE(Tree.TEMP h, limit),
    									 Tree.LABEL start,
    									 Tree.CJUMP(Tree.LE, Tree.TEMP r, Tree.TEMP h, t, false_label),
                       Tree.LABEL false_label',
                       Tree.JUMP(Tree.NAME(false_label), [false_label]),
    									 Tree.LABEL t,
    									 bodyNx,
                       Tree.CJUMP(Tree.EQ, Tree.TEMP r, Tree.TEMP h, false_label, cont),
                       Tree.LABEL cont,
    									 Tree.MOVE(Tree.TEMP r, Tree.BINOP(Tree.PLUS, Tree.TEMP r, Tree.CONST 1)),
                       Tree.JUMP(Tree.NAME(t), [t]),
    									 Tree.LABEL false_label])
		end

    fun translateSubscriptVar (var_exp, index_exp) =
      let
        val var = unEx var_exp
        val index = unEx index_exp
        val size_reg = Temp.newtemp()
        val out_of_bounds = Temp.newlabel()
        val in_bounds_init = Temp.newlabel()
        val in_bounds = Temp.newlabel()
      in
        Ex(Tree.ESEQ(Tree.SEQ([Tree.MOVE(Tree.TEMP size_reg, Tree.MEM(Tree.BINOP(Tree.MINUS, var, Tree.CONST Frame.wordSize))),
                               Tree.CJUMP(Tree.GE, index, Tree.CONST 0, in_bounds_init, out_of_bounds),
                               Tree.LABEL out_of_bounds,
                               unNx (Ex(Frame.externalCall ("exit", [Tree.CONST 1]))),
                               Tree.LABEL in_bounds_init,
                               Tree.CJUMP(Tree.LT, index, Tree.TEMP size_reg, in_bounds, out_of_bounds),
                               Tree.LABEL in_bounds
                              ]),
                    Tree.MEM (Tree.BINOP(Tree.PLUS, var, Tree.BINOP(Tree.MUL, index, Tree.CONST(Frame.wordSize))))
                    )
          )
      end

		fun translateArray (size, init) =
      let
        val arr_pointer = Frame.externalCall ("tig_initArray", [Tree.BINOP(Tree.PLUS, unEx size, Tree.CONST 1), unEx init])
        val arr_pointer' = Temp.newtemp()
      in
        Ex (Tree.ESEQ(Tree.SEQ([Tree.MOVE(Tree.TEMP arr_pointer', arr_pointer),
                                Tree.MOVE(Tree.MEM(Tree.TEMP arr_pointer'), unEx size)]),
                                Tree.BINOP(Tree.PLUS, Tree.TEMP arr_pointer', Tree.CONST Frame.wordSize)
                     )
           )
      end

		fun translateSequence exprs = case exprs of
				[]     => Ex (Tree.CONST 0)
      | [h]   => Ex (unEx h)
			| h::l => Ex (Tree.ESEQ(unNx h, unEx (translateSequence l)))

		fun translateString lit =
			let
				fun is_frag_equal item = case item of
						Frame.PROC(_) => false
					| Frame.STRING(lab', lit') => if String.compare(lit', lit) = EQUAL then true else false
				fun check_list () = case List.find is_frag_equal (!fragments) of
				 												SOME(Frame.STRING(lab', lit')) => lab'
															| _ => let
																				val lab' = Temp.newlabel()
																			in
																				(fragments := (Frame.STRING(lab', lit))::(!fragments); lab')
																			end
				val lab = check_list()
			in
				Ex (Tree.NAME(lab))
			end

		fun translateRecord exprs =
			let
				val size = length exprs * Frame.wordSize
				val r = Temp.newtemp()
				val pointer = Frame.externalCall("tig_allocRecord", [(Tree.CONST size)])
				fun buildTranslation ([], currentList) = currentList
					| buildTranslation (h::l, currentList) =
                        buildTranslation (l,
                                          (Tree.MOVE(
                                            Tree.MEM(
                                              Tree.BINOP(
                                                Tree.PLUS,
                                                Tree.TEMP r,
                                                Tree.CONST (((size - ((length l) + 1)* Frame.wordSize)))
                                              )
                                            ),
                                            unEx h)::currentList
                                           )
                                          )
			in
				Ex (Tree.ESEQ(Tree.SEQ(Tree.MOVE(Tree.TEMP r, pointer):: (rev (buildTranslation (exprs, [])))), Tree.TEMP r))
			end

    fun translateLet(expList, body_exp) =
      let
        fun buildStmList(a::l) = unNx(a)::buildStmList(l)
          | buildStmList [] = []
      in
        Ex(Tree.ESEQ(Tree.SEQ(buildStmList expList), unEx body_exp))
      end

		fun resetFragList() = fragments := []

    fun procEntryExit {level=level, body=body} =
      let
        val frame =
          case level of
              TOP => (ErrorMsg.error 0 "FunDec cannot occur in outermost level.";
                           Frame.newFrame {name=Temp.newlabel(), formals=[]})
            | LEV({unique, parent, frame=frame}) => frame
        val resultProcEntryExit = Frame.procEntryExit1(frame, unEx body)
        val body' = #1 resultProcEntryExit
        val offset = ref (#3 resultProcEntryExit)
        fun restoreCalleeReg (reg) = (offset := !offset - Frame.wordSize;
                                      Tree.MOVE(Tree.TEMP reg, Tree.MEM(Tree.BINOP(Tree.PLUS, Tree.TEMP Frame.FP, Tree.CONST (!offset)))))
        val restoreRA = Tree.MOVE(Tree.TEMP Frame.RA, Tree.MEM(Tree.BINOP(Tree.PLUS, Tree.TEMP Frame.FP, Tree.CONST (#2 resultProcEntryExit))))
        val restoreCalleeStms = map restoreCalleeReg (Frame.get_registers Frame.calleesaves)
        val restoreFP = Tree.MOVE(Tree.TEMP Frame.FP, Tree.MEM(Tree.BINOP(Tree.PLUS, Tree.TEMP Frame.FP, Tree.CONST (#3 resultProcEntryExit))))
        val restoreSP = Tree.MOVE(Tree.TEMP Frame.SP, Tree.BINOP(Tree.PLUS, Tree.TEMP Frame.SP, Tree.CONST (#4 resultProcEntryExit)))
        val rv_body' = Tree.SEQ([Tree.MOVE(Tree.TEMP(Frame.RV), body'), restoreRA] @ restoreCalleeStms @ [restoreFP, restoreSP])
      in
        fragments := Frame.PROC({body=rv_body', frame=frame})::(!fragments)
      end

    fun getResult() =
		 	let
				val mylist = !fragments
			in
				resetFragList();
				mylist
			end


end
