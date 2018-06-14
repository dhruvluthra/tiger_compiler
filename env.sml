signature ENV =
sig
	(* type access *)
	type ty
	datatype enventry = VarEntry of {access: Translate.access, ty:ty, iterator:bool}
					  | FunEntry of {level: Translate.level, label: Temp.label, formals: ty list, result: ty}
	val base_tenv : ty Symbol.table
	val base_venv: enventry Symbol.table
end

structure Env : ENV =
struct

	structure Tr = Translate
	(* type access *)
	type ty = Types.ty
	datatype enventry = VarEntry of {access: Translate.access, ty:ty, iterator:bool}
					  | FunEntry of {level: Translate.level, label: Temp.label, formals: ty list, result: ty}

	(* List of symbol * type tuples *)
	val initial_types = [(Symbol.symbol("int"), Types.INT),
						 (Symbol.symbol("string"), Types.STRING)]

	(* List of symbol * enventry tuples *)
	val initial_functions = [(Symbol.symbol("print"), FunEntry({level = Tr.outermost, label = Temp.newlabel(), formals=[Types.STRING], result=Types.UNIT})),
							 (Symbol.symbol("flush"), FunEntry({level = Tr.outermost, label = Temp.newlabel(), formals=[], result=Types.UNIT})),
							 (Symbol.symbol("getchar"), FunEntry({level = Tr.outermost, label = Temp.newlabel(), formals=[], result=Types.STRING})),
							 (Symbol.symbol("ord"), FunEntry({level = Tr.outermost, label = Temp.newlabel(), formals=[Types.STRING], result=Types.INT})),
							 (Symbol.symbol("chr"), FunEntry({level = Tr.outermost, label = Temp.newlabel(), formals=[Types.INT], result=Types.STRING})),
							 (Symbol.symbol("size"), FunEntry({level = Tr.outermost, label = Temp.newlabel(), formals=[Types.STRING], result=Types.INT})),
							 (Symbol.symbol("substring"), FunEntry({level = Tr.outermost, label = Temp.newlabel(), formals=[Types.STRING, Types.INT, Types.INT], result=Types.STRING})),
							 (Symbol.symbol("concat"), FunEntry({level = Tr.outermost, label = Temp.newlabel(), formals=[Types.STRING, Types.STRING], result=Types.STRING})),
							 (Symbol.symbol("not"), FunEntry({level = Tr.outermost, label = Temp.newlabel(), formals=[Types.INT], result=Types.INT})),
							 (Symbol.symbol("exit"), FunEntry({level = Tr.outermost, label = Temp.newlabel(), formals=[Types.INT], result=Types.UNIT}))]

	fun add_initial((sym, entry), currtable) = Symbol.enter(currtable, sym, entry)

	val base_tenv = foldl add_initial Symbol.empty initial_types
	val base_venv = foldl add_initial Symbol.empty initial_functions

end
