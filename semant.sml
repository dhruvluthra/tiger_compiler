structure Semant =
struct

	structure A = Absyn
	structure S = Symbol
	structure E = ErrorMsg
	structure Tr = Translate

	type venv = Env.enventry S.table
	type tenv = Env.ty S.table
	type expty = {exp: Tr.exp, ty: Types.ty}

	fun is_stndrd_lbry func =
		let
				val stndrd_lbry = ["print",
													 "flush",
													 "getchar",
													 "ord",
													 "chr",
													 "size",
													 "substring",
													 "concat",
													 "not",
													 "exit"]
		in
			List.exists (fn x => x = (S.name func)) stndrd_lbry
		end


	fun get_actual_ty (ty, pos) =
  		case ty of
  				Types.NAME(sym, ref(SOME(some_ty))) => get_actual_ty(some_ty, pos)
  		|		Types.NAME(sym, ref(NONE)) => (E.error pos ("Undefined type: " ^ S.name sym);
  		 																	 Types.UNIT)
  		|		ty => ty

	fun check_int ({exp, ty}, pos) =
		let
				val actual_ty = get_actual_ty (ty, pos)
		in
				if get_actual_ty (ty, pos) = Types.INT
				then ()
				else E.error pos ("Integer required, type given: " ^ (Types.type_to_string actual_ty))
		end

	fun check_int_or_string ({exp, ty}, pos) =
		let val actual_ty = get_actual_ty (ty, pos)
		in
			if actual_ty = Types.INT
			then ()
			else (if actual_ty = Types.INT
						then ()
						else (E.error pos ("Integer or string required, type given: " ^ (Types.type_to_string actual_ty))))
		end

	fun check_unit ({exp, ty}, pos) =
		if get_actual_ty (ty, pos) = Types.UNIT
		then ()
		else (E.error pos "Should not produce value")

	fun check_same_type (ty1:Types.ty, ty2:Types.ty, pos) =
		let
			val actual_ty1 = get_actual_ty (ty1, pos)
			val actual_ty2 = get_actual_ty (ty2, pos)
		in
			(if actual_ty1 = actual_ty2
			 then true
 		 	 else (
				 (case actual_ty1 of
	 				   Types.RECORD(fields, unique) => (
	 							if actual_ty2 = Types.NIL
	 							then true
	 							else (E.error pos "Types don't match";
	 										false))
	 				 | Types.NIL => (
	 					 		case actual_ty2 of
	 								Types.RECORD(fields, unique) => true
	 							| _ => (E.error pos ("Types don't match: " ^
		 					 											 (Types.type_to_string actual_ty1) ^
		 																 " and " ^
		 																 (Types.type_to_string actual_ty2));
	 										 false))
	 				 | _ => (E.error pos "Types don't match";
	 								false))
				 )
			)
	end

	fun get_type_to_ref (t_env, sym, pos) =
			case S.look(t_env, sym) of
			    SOME(ty) => SOME(ty)
				| NONE => (E.error pos ("Undefined type: " ^ S.name sym);
				 					 SOME(Types.UNIT))

	fun sym_to_type (t_env, sym, pos) =
		case S.look(t_env, sym) of
				SOME(Types.NAME(sym, ref(SOME(ty)))) => get_actual_ty(ty, pos)
			| SOME(Types.NAME(sym, ref(NONE))) => (E.error pos ("Undefined type: " ^ S.name sym);
			 																			 Types.UNIT)
			| SOME(ty) => ty
		  |	NONE => (E.error pos ("Undefined type: " ^ S.name sym);
				 				 Types.UNIT)

	fun varsym_to_expty (v_env, sym, pos, level) =
		case S.look(v_env, sym) of
				SOME(Env.VarEntry{access, ty, iterator}) =>
					{exp=Tr.translateSimpleVar(access, level), ty=(get_actual_ty (ty, pos))}
			| SOME(Env.FunEntry{level, label, formals, result}) =>
					(E.error pos ("Function call incomplete: " ^ S.name sym);
					 {exp=Tr.translateNil(), ty=Types.INT})
			|	NONE =>
					(E.error pos ("Undefined variable: " ^ S.name sym);
					 {exp=Tr.translateNil(), ty=Types.INT})

	fun funsym_to_expty (v_env, sym, pos, level) =
		case S.look(v_env, sym) of
				SOME(Env.VarEntry{access, ty, iterator}) =>
					(E.error pos ("Cannot call variable name as function: " ^ S.name sym);
					 {level=level, label=Temp.newlabel(), formals=[], result_ty=Types.INT})
			| SOME(Env.FunEntry{level, label, formals, result}) =>
					{level=level, label=label, formals=formals, result_ty=(get_actual_ty (result, pos))}
			|	NONE =>
					(E.error pos ("Undefined variable: " ^ S.name sym);
					 {level=level, label=Temp.newlabel(), formals=[], result_ty=Types.INT})


	fun transVar (v_env, t_env, loop_option, level) =
		let fun trvar (A.SimpleVar(id, pos)) = varsym_to_expty(v_env, id, pos, level)
					| trvar (A.FieldVar(var, id, pos)) =
							  let
									val {exp=var_exp, ty=ty} = trvar var
									fun indexOf ([], id, cur) = cur
										|	indexOf ((sym, typ)::l, id, cur) = if sym=id then cur else indexOf(l, id, cur+1)
									fun check_fields ([], total_fields) =
											(E.error pos ("Undefined field: " ^ S.name id);
											{exp=Tr.translateNil(), ty=Types.UNIT})
									  | check_fields (((sym, typ)::fields), total_fields) =
												if sym = id
												then {exp=Tr.translateFieldVar(var_exp, indexOf(total_fields, id, 0)), ty=typ}
												else check_fields (fields, total_fields)
								in
									case get_actual_ty (ty, pos) of
										  Types.RECORD(fields, unique) => check_fields (fields, fields)
									  	| _ => (E.error pos ("Variable does not have fields");
									 					{exp=Tr.translateNil(), ty=Types.UNIT})
								end
					 | trvar (A.SubscriptVar(var, index, pos)) =
					 			let
									val {exp=var_exp, ty=var_ty} = trvar var
									val {exp=index_exp, ty=index_ty} = transExp (v_env, t_env, loop_option, level) index
								in
									case get_actual_ty (var_ty, pos) of
										  Types.ARRAY(typ, unique) =>
													 (check_int({exp=index_exp, ty=index_ty}, pos);
													  {exp=Tr.translateSubscriptVar(var_exp, index_exp), ty=typ})
									  | _ => (E.error pos ("Variable cannot be indexed");
									 					{exp=Tr.translateNil(), ty=Types.UNIT})
								end
		in
			trvar
		end

	and transExp (v_env, t_env, loop_option, level) =
		let fun trexp (A.VarExp(v)) = transVar(v_env, t_env, loop_option, level) v
		      | trexp (A.NilExp) = {exp=Tr.translateNil(), ty=Types.NIL}
				  | trexp (A.IntExp(i)) = {exp=Tr.translateInt(i), ty=Types.INT}

				  | trexp (A.StringExp(s, pos)) = {exp=Tr.translateString(s), ty=Types.STRING}

					| trexp (A.OpExp{left, oper=A.PlusOp, right, pos}) =
							let
									val left_expty = trexp left
									val right_expty = trexp right
							in
									(check_int(left_expty, pos);
									 check_int(right_expty, pos);
									 {exp=Tr.translateBinOp(A.PlusOp, #exp left_expty, #exp right_expty), ty=Types.INT})
							end
					| trexp (A.OpExp{left, oper=A.MinusOp, right, pos}) =
							let
									val left_expty = trexp left
									val right_expty = trexp right
							in
									(check_int(left_expty, pos);
									 check_int(right_expty, pos);
									 {exp=Tr.translateBinOp(A.MinusOp, #exp left_expty, #exp right_expty), ty=Types.INT})
							end
					| trexp (A.OpExp{left, oper=A.TimesOp, right, pos}) =
							let
									val left_expty = trexp left
									val right_expty = trexp right
							in
									(check_int(left_expty, pos);
									 check_int(right_expty, pos);
									 {exp=Tr.translateBinOp(A.TimesOp, #exp left_expty, #exp right_expty), ty=Types.INT})
							end
					| trexp (A.OpExp{left, oper=A.DivideOp, right, pos}) =
							let
									val left_expty = trexp left
									val right_expty = trexp right
							in
									(check_int(left_expty, pos);
									 check_int(right_expty, pos);
									 {exp=Tr.translateBinOp(A.DivideOp, #exp left_expty, #exp right_expty), ty=Types.INT})
							end
					| trexp (A.OpExp{left, oper=A.LtOp, right, pos}) =
							let
									val left_expty = trexp left
									val right_expty = trexp right
							in
									(check_int(left_expty, pos);
									 check_int(right_expty, pos);
									 {exp=Tr.translateRelOp(A.LtOp, #exp left_expty, #exp right_expty, false), ty=Types.INT})
							end
					| trexp (A.OpExp{left, oper=A.LeOp, right, pos}) =
							let
									val left_expty = trexp left
									val right_expty = trexp right
							in
									(check_int(left_expty, pos);
									 check_int(right_expty, pos);
									 {exp=Tr.translateRelOp(A.LeOp, #exp left_expty, #exp right_expty, false), ty=Types.INT})
							end
					| trexp (A.OpExp{left, oper=A.GtOp, right, pos}) =
							let
									val left_expty = trexp left
									val right_expty = trexp right
							in
									(check_int(left_expty, pos);
									 check_int(right_expty, pos);
									 {exp=Tr.translateRelOp(A.GtOp, #exp left_expty, #exp right_expty, false), ty=Types.INT})
							end
					| trexp (A.OpExp{left, oper=A.GeOp, right, pos}) =
							let
									val left_expty = trexp left
									val right_expty = trexp right
							in
									(check_int(left_expty, pos);
									 check_int(right_expty, pos);
									 {exp=Tr.translateRelOp(A.GeOp, #exp left_expty, #exp right_expty, false), ty=Types.INT})
							end
					| trexp (A.OpExp{left, oper=A.EqOp, right, pos}) =
							let
									val left_expty = trexp left
									val right_expty = trexp right
							in
									(check_int_or_string(left_expty, pos);
									 check_int_or_string(right_expty, pos);
									 check_same_type(#ty (left_expty), #ty (right_expty), pos);
									 {exp=Tr.translateRelOp(A.EqOp, #exp left_expty, #exp right_expty, (#ty (left_expty)) = Types.STRING), ty=Types.INT})
							end
					| trexp (A.OpExp{left, oper=A.NeqOp, right, pos}) =
							let
									val left_expty = trexp left
									val right_expty = trexp right
							in
									(check_int_or_string(left_expty, pos);
									 check_int_or_string(right_expty, pos);
									 check_same_type(#ty (left_expty), #ty (right_expty), pos);
									 {exp=Tr.translateRelOp(A.NeqOp, #exp left_expty, #exp right_expty, (#ty (left_expty)) = Types.STRING), ty=Types.INT})
							end

					| trexp (A.RecordExp{fields, typ, pos}) =
				  			let
				  				fun build_type ((sym, exp, pos), rec_typ) =
				  					let val t = #ty (trexp exp)
				  					in (sym, t)::rec_typ
				  					end
				  				val exp_fields = foldr build_type [] fields
				  				fun compare ([], [], pos) = ()
										| compare ((ename:S.symbol, etyp:Types.ty)::expfields, (name:S.symbol, typ:Types.ty)::typfields, pos) =
												(if (ename = name) andalso check_same_type(etyp, typ, pos)
												 then compare(expfields, typfields, pos)
												 else ())
										| compare (_,_,pos) = (E.error pos ("Record does not have correct number of fields"); ())
									 val typ_ty = sym_to_type(t_env, typ, pos)
									 fun build_exps ((sym, exp, pos), rec_exps) =
	 				  					let val e = #exp (trexp exp)
	 				  					in e::rec_exps
	 				  					end
									 val exps = foldr build_exps [] fields
								in
					  			case typ_ty of
					  				  Types.RECORD(typ_fields, unique) =>
													(compare(exp_fields, typ_fields, pos);
						  					   {exp=Tr.translateRecord(exps), ty=typ_ty})
					  			  | Types.UNIT => {exp=Tr.translateNil(), ty=Types.RECORD(exp_fields, ref ())}
					  			  | _ =>
					  			  		(E.error pos ("Types don't match: record and " ^ (Types.type_to_string typ_ty));
					  			  		 {exp=Tr.translateNil(), ty=Types.RECORD(exp_fields, ref ())})
					  		end
					| trexp (A.SeqExp(seq)) =
								let fun process_seq ([], ir_list) = {ir_list = ir_list, ty=Types.UNIT}
											| process_seq ((exp, pos)::[], ir_list) =
													let
														val last_expty = trexp exp
													in
														{ir_list = ir_list@[#exp last_expty], ty=(#ty last_expty)}
													end
											| process_seq ((exp, pos)::seq, ir_list) =
													let
														val midseq_expty = trexp exp
													in
															 process_seq(seq, ir_list@[#exp midseq_expty])
													end
										val irlist_type = process_seq(seq, [])
								in
										{exp=Tr.translateSequence(#ir_list irlist_type), ty=(#ty irlist_type)}
								end
				 | trexp (A.AssignExp{var, exp, pos}) =
				 				let
										val exp_expty = trexp exp
										val var_expty =
												case var of
														A.SimpleVar(id, pos) =>
																(case S.look(v_env, id) of
																		SOME(Env.VarEntry{access, ty, iterator}) =>
																				(case iterator of
																						false => {exp=Tr.translateSimpleVar(access, level), ty=(get_actual_ty (ty, pos))}
																					| true => (E.error pos ("Iterator variables may not be assigned to: " ^ S.name id);
																										 {exp=Tr.translateSimpleVar(access, level), ty=(get_actual_ty (ty, pos))}))
																	| SOME(Env.FunEntry{level, label, formals, result}) =>
																			(E.error pos ("Function variables may not be assigned to: " ^ S.name id);
																			 {exp=Tr.translateNil(), ty=Types.INT})
																	|	NONE =>
																			(E.error pos ("Undefined variable: " ^ S.name id);
																			 {exp=Tr.translateNil(), ty=Types.INT}))
													| _ => transVar (v_env, t_env, loop_option, level) var
								 in
										 (check_same_type(#ty var_expty, #ty exp_expty, pos);
											{exp=Tr.translateAssign(#exp var_expty, #exp exp_expty), ty=Types.UNIT})
								 end
				  | trexp (A.IfExp{test, then', else'=NONE, pos}) =
								let
									val condition_expty = trexp test
									val true_case_expty = trexp then'
								in
									(check_int(condition_expty, pos);
									 check_unit(true_case_expty, pos);
									 {exp=Tr.translateIf(#exp condition_expty, #exp true_case_expty, Tr.translateSequence([])),
										ty=Types.UNIT})
								end
				  | trexp (A.IfExp{test, then', else'=SOME(e), pos}) =
				  			let
									val condition_expty = trexp test
									val true_case_expty = trexp then'
									val false_case_expty = trexp e
				  			in
				  				(check_int(condition_expty, pos);
				  			 	 check_same_type(#ty true_case_expty, #ty false_case_expty, pos);
				  			 	 {exp=Tr.translateIf(#exp condition_expty, #exp true_case_expty, #exp false_case_expty),
										ty=(#ty true_case_expty)})
				  			end
				  | trexp (A.WhileExp{test, body, pos}) =
							let
									val condition_expty = trexp test
									val false_label = Temp.newlabel()
									val body_expty = transExp(v_env, t_env, SOME(false_label), level) body
							in
									(check_int(condition_expty, pos);
									 check_unit(body_expty, pos);
									 {exp=Tr.translateWhile(#exp condition_expty, #exp body_expty, false_label), ty=Types.UNIT})
							end
				  | trexp (A.ForExp{var, escape, lo, hi, body, pos}) =
							let
								val lo_expty = trexp lo
								val hi_expty = trexp hi
								val access = Tr.allocLocal(level)(!escape)
								val {venv=v_env', tenv=t_env'} = {tenv=t_env, venv=S.enter(v_env, var, Env.VarEntry{access=access, ty=Types.INT, iterator=true})}
								val var_exp = Tr.translateSimpleVar(access, level)
								val false_label = Temp.newlabel()
								val body_expty = transExp(v_env', t_env', SOME(false_label), level) body
							in
								(check_int(lo_expty, pos);
							 	 check_int(hi_expty, pos);
							 	 check_unit(body_expty, pos);
							 	 {exp=Tr.translateFor(var_exp, escape, #exp lo_expty, #exp hi_expty, #exp body_expty, false_label), ty=Types.UNIT})
							end
					| trexp (A.BreakExp(pos)) =
							(case loop_option of
								 SOME(l) => {exp=Tr.translateBreak(l), ty=Types.UNIT}
							 | NONE => (E.error pos ("Break must be within a loop");
												 {exp=Tr.translateBreak(Temp.newlabel()), ty=Types.UNIT}))
					| trexp (A.LetExp{decs, body, pos}) =
				  			let
									val expList = ref []
				  				fun add_dec (dec, {venv=v, tenv=t}) =
												let
													val {venv=venv, tenv=tenv, exp=assign_exp} = transDec(v, t, loop_option, pos, level) dec
												in
													case dec of
														A.VarDec(x) => (expList := (!expList)@[assign_exp]; {venv=venv, tenv=tenv})
														| _	=> {venv=venv, tenv=tenv}
												end
				  				val {venv=v_env', tenv=t_env'} = foldl add_dec {venv=v_env, tenv=t_env} decs
									val {exp=body_exp, ty=body_ty} = transExp(v_env', t_env', loop_option, level) body
				  			in
				  				{exp=Tr.translateLet(!expList, body_exp), ty=body_ty}
				  			end
					| trexp (A.ArrayExp{typ, size, init, pos}) =
							let
								val array_ty = sym_to_type (t_env, typ, pos)
								val size_expty = trexp size
								val init_expty = trexp init
							in
								(check_int(size_expty, pos);
								 case array_ty of
									 	Types.ARRAY(typ, unique) =>
									 				(check_same_type(get_actual_ty (typ,pos), get_actual_ty (#ty init_expty,pos), pos);
													{exp=Tr.translateArray(#exp size_expty, #exp init_expty), ty=array_ty})
										| _ => (E.error pos ("Array type required, type given: " ^ (Types.type_to_string array_ty));
													{exp=Tr.translateNil(), ty=Types.ARRAY(#ty init_expty, ref ())}))
							end
					| trexp (A.CallExp{func, args, pos}) =
							let
								val {level=fun_level, label, formals, result_ty} = funsym_to_expty(v_env, func, pos, level)
								fun eval_arg (arg) = transExp(v_env, t_env, loop_option, level) arg
								val arg_types = map #ty (map eval_arg args)
								val arg_exps = map #exp (map eval_arg args)
								fun get_actual_types (t, l) = get_actual_ty(t, pos)::l
								val actual_arg_types = foldr get_actual_types [] arg_types
								val actual_formal_types = foldr get_actual_types [] formals
							in
								if ((List.length actual_arg_types) = (List.length actual_formal_types))
								then (if actual_arg_types = actual_formal_types
											then (if (is_stndrd_lbry func)
														then {exp=Tr.translateStdrdLbryCall(func, arg_exps), ty=result_ty}
														else {exp=Tr.translateCall(fun_level, level, label, arg_exps), ty=result_ty}

											)
											else (E.error pos ("Type mismatch in function parameter inputs");
																{exp=Tr.translateNil(), ty=result_ty}))
								else (E.error pos ("Incorrect number of function parameter inputs.");
													{exp=Tr.translateNil(), ty=result_ty})
							end
		in
			trexp
		end

	and transTy (t_env, id, pos) =
		let fun trty (A.NameTy(sym, pos)) =
						(case S.look(t_env, id) of
								SOME(Types.NAME(defined_type, r)) => (
										let
											val () = r := get_type_to_ref(t_env, sym, pos)
										in
											Types.UNIT
										end)
							| _ => E.impossible "Types should all be added as Types.NAME to t_env in transDec")
					| trty (A.RecordTy(fields)) =
						let
							fun build_record ({name, typ, escape, pos}, curr_f_list) =
									(name, Types.NAME(name, ref (get_type_to_ref(t_env, typ, pos))))::curr_f_list
							fun duplicated [] = false
									| duplicated (x::xs) = (List.exists (fn y => x = y) xs) orelse (duplicated xs)
							fun make_names_list ({name, typ, escape, pos}, ans) = name::ans
							val names_list = foldr make_names_list [] fields
							val translated_field_list = foldr build_record [] fields
						in
							if duplicated(names_list) then E.error pos ("Invalid duplicate record fields") else ();
							(case S.look(t_env, id) of
								SOME(Types.NAME(defined_type, r)) => (
									let
										val () = r:= SOME(Types.RECORD(translated_field_list, ref()))
									in
										Types.UNIT
									end)
							 | _ => E.impossible "Types should all be added as Types.NAME to t_env in transDec")
						end
					| trty (A.ArrayTy(sym, pos)) =
						(case S.look(t_env, id) of
								SOME(Types.NAME(defined_type, r)) =>
									let
										val () = r:= SOME(Types.ARRAY(valOf (get_type_to_ref(t_env, sym, pos)), ref()))
									in
										Types.UNIT
									end
							| _ => E.impossible "Types should all be added as Types.NAME to t_env in transDec")
		in
			trty
		end



	and transDec (v_env, t_env, loop_option, pos, level) =

		let fun trdec (A.VarDec{name, escape, typ=NONE, init, pos}) =
							let val {exp=init_exp, ty} = transExp(v_env, t_env, loop_option, level) init
									val access = Tr.allocLocal(level)(!escape)
									val left = Tr.translateSimpleVar(access, level)
							in
								case ty of
										Types.NIL => (E.error pos ("Cannot assign nil to non-record type");
																		{tenv=t_env, venv=S.enter(v_env, name, Env.VarEntry{access=access, ty=ty, iterator=false}), exp=Tr.translateNil()})
								|   _         => {tenv=t_env, venv=S.enter(v_env, name, Env.VarEntry{access=access, ty=ty, iterator=false}), exp=Tr.translateAssign(left, init_exp)}
							end
			    | trdec (A.VarDec{name, escape, typ=SOME(t), init, pos}) =
							let
								val {exp=init_exp, ty} = transExp(v_env, t_env, loop_option, level) init
								val (typ_sym, typ_pos) = t
								val access = Tr.allocLocal(level)(!escape)
								val left = Tr.translateSimpleVar(access, level)
							in
								(check_same_type(sym_to_type(t_env, typ_sym, typ_pos), get_actual_ty (ty, pos), pos);
								 {tenv=t_env,
								  venv=S.enter(v_env, name, Env.VarEntry{access=access, ty=ty, iterator=false}), exp=Tr.translateAssign(left, init_exp)})
							end
				| trdec (A.TypeDec(decs)) =
							let
			  				fun add_dec ({name, ty, pos}, {venv, tenv}) =
									(case S.look(tenv, name) of
											SOME(Types.NAME(defined_type, ref NONE)) => (E.error pos ("Invalid duplicate type declaration: " ^ S.name name);
																																			{venv=venv, tenv=S.enter(tenv, name, Types.NAME(name, ref NONE))})
										| _ => {venv=venv, tenv=S.enter(tenv, name, Types.NAME(name, ref NONE))} )

								val new_envs = foldl add_dec {venv=v_env, tenv=t_env} decs

								fun fill_body ({name, ty, pos}, {venv, tenv}) =
									 (transTy (tenv, name, pos) ty;
									  {venv=venv, tenv = tenv})
								val {venv=final_venv, tenv=final_tenv} = foldl fill_body new_envs decs
								fun check_cycles ({name, ty, pos}, cycles_found) =
										let
											val cycle_already_found = List.exists (fn y => name = y) cycles_found
											fun look_for_none (ty, pos, curr_cycle) =
													(case ty of
												    SOME(Types.NAME(sym, ref(SOME(some_ty)))) =>
																	(let
																			val cycle = List.exists (fn y => sym = y) curr_cycle
																			val new_curr_cycle = sym::curr_cycle
																	 in
																		 	(if cycle
																			 then (let
																								val cycle_string = foldr (fn (v, s) => s ^ " " ^ S.name v) "" curr_cycle
																						 in
																				 		 		if name = sym
																								then (E.error pos ("Invalid cycle:" ^ cycle_string); curr_cycle @ cycles_found)
																								else cycles_found
																						 end)
																			 else look_for_none(SOME(some_ty), pos, new_curr_cycle))
																	 end)
													| SOME(Types.NAME(sym, ref(NONE))) => (E.impossible "Should be caught in transTy"; cycles_found)
													|	ty => cycles_found)
										in
												if cycle_already_found
												then cycles_found
												else look_for_none(S.look(final_tenv, name), pos, [])
										end
			  			in
								 (foldl check_cycles [] decs;
									{venv=final_venv, tenv=final_tenv, exp=Tr.translateNil()})
							end

				| trdec (A.FunctionDec(fundecs)) =
							let
								fun add_dec_header ({name, params, result=NONE, body, pos}, {venv, tenv}) =
												let
													fun duplicated [] = false
														| duplicated (x::xs) = (List.exists (fn y => x = y) xs) orelse (duplicated xs)
													fun transparam({name, escape, typ, pos}) =
																				{name=name, ty=sym_to_type(tenv, typ, pos), escape=(!escape)}
													fun make_names_list ({name, escape, typ, pos}, ans) = name::ans
													val names_list = foldr make_names_list [] params
													val params' = (if duplicated(names_list) then E.error pos ("Invalid duplicate function parameters") else ();
																				map transparam params)
													val result_ty = Types.UNIT
													val new_label = Temp.newlabel()
													val formals_escape = map #escape params'
													val new_level = Tr.newLevel({parent=level, name=new_label, formals=formals_escape})
													val venv' = S.enter(venv, name,
																		Env.FunEntry{level=new_level, label=new_label, formals=map #ty params',result=result_ty})
												in
													{venv=venv', tenv=tenv}
												end
									|	add_dec_header ({name, params, result=SOME(res_sym,res_pos), body, pos},
												{venv, tenv}) =
												let
													fun duplicated [] = false
															| duplicated (x::xs) = (List.exists (fn y => x = y) xs) orelse (duplicated xs)
													fun transparam({name, escape, typ, pos}) =
																					{name=name, ty=sym_to_type(tenv, typ, pos), escape=(!escape)}
													fun make_names_list ({name, escape, typ, pos}, ans) = name::ans
													val names_list = foldr make_names_list [] params
													val params' = (if duplicated(names_list) then E.error pos ("Invalid duplicate function parameters") else ();
																					map transparam params)
													val result_ty = sym_to_type(tenv, res_sym, res_pos)
													val new_label = Temp.newlabel()
													val formals_escape = map #escape params'
													val new_level = Tr.newLevel({parent=level, name=new_label, formals=formals_escape})
													val venv' = S.enter(venv, name,
																		Env.FunEntry{level=new_level, label=new_label, formals=map #ty params',result=result_ty})
												in
													{venv=venv', tenv=tenv}
												end
								fun add_dec_body ({name, params, result=NONE, body, pos}, {venv, tenv}) =
												let
													fun transparam({name, escape, typ, pos}) =
																				{name=name, ty=sym_to_type(tenv, typ, pos), escape=escape}
													val params' = map transparam params
													val result_ty = Types.UNIT
													val func_entry_opt = S.look(venv, name)
													val func_level =
															case func_entry_opt of
																	SOME(Env.FunEntry{level, label, formals, result}) => level
																	| _ => level
													fun enterparam({name, ty, escape}, (venv, curr)) =
															let
																	val formal_accesses = Tr.formals func_level
															in
																	(S.enter(venv, name, Env.VarEntry{access=List.nth(formal_accesses, curr), ty=ty, iterator=false}), curr+1)
															end
													val venv' = #1 (foldl enterparam (venv,1) params')
													val {exp=body_exp, ty=body_ty} = transExp(venv', tenv, loop_option, func_level) body
												in
													check_same_type(body_ty, result_ty, pos);
													Tr.procEntryExit{level=func_level, body=body_exp};
													{venv=venv, tenv=tenv}
												end
									| add_dec_body ({name, params, result=SOME(res_sym,res_pos), body, pos},
													{venv, tenv}) =
												let
													fun transparam({name, escape, typ, pos}) =
																				{name=name, ty=sym_to_type(tenv, typ, pos), escape=escape}
													val params' = map transparam params
													val result_ty = sym_to_type(tenv, res_sym, res_pos)
													val func_entry_opt = S.look(venv, name)
													val func_level =
															case func_entry_opt of
																	SOME(Env.FunEntry{level, label, formals, result}) => level
																	| _ => level
													fun enterparam({name, ty, escape}, (venv, curr)) =
														let
															val formal_accesses = Tr.formals func_level
															val curr_access = List.nth(formal_accesses, curr)
														in
															(S.enter(venv, name, Env.VarEntry{access=curr_access, ty=ty, iterator=false}), curr+1)
														end
													val venv' = #1 (foldl enterparam (venv,1) params')
													val {exp=body_exp, ty=body_ty} = transExp(venv', tenv, loop_option, func_level) body
												in
													check_same_type(body_ty, result_ty, pos);
													Tr.procEntryExit{level=func_level, body=body_exp};
													{venv=venv, tenv=tenv}
												end

							in
								let
										fun make_names_list ({name, params, result, body, pos}, ans) = name::ans
										val names_list = foldr make_names_list [] fundecs
										fun duplicated [] = false
											| duplicated (x::xs) = (List.exists (fn y => x = y) xs) orelse (duplicated xs)
										val {venv=final_venv, tenv=final_tenv} = foldl add_dec_body (foldl add_dec_header {venv=v_env, tenv=t_env} fundecs) fundecs
								 in
									 	if duplicated(names_list) then E.error pos ("Invalid duplicate function declaration") else ();
										{venv=final_venv, tenv=final_tenv, exp=Tr.translateNil()}
								 end
							end
		in
			trdec
		end


	fun transProg ast =
		let
			val v_env = Env.base_venv
			val t_env = Env.base_tenv
			val init_level = Tr.newLevel({parent=Tr.outermost, name=Temp.newlabel(), formals=[]})
		in
			Tr.procEntryExit {level=init_level, body= #exp (transExp (v_env, t_env, NONE, init_level) ast)};
			Tr.getResult()
		end

end
