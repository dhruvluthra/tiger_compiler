structure Types =
struct

  type unique = unit ref

  datatype ty =
            RECORD of (Symbol.symbol * ty) list * unique
          | NIL
          | INT
          | STRING
          | ARRAY of ty * unique
	        | NAME of Symbol.symbol * ty option ref
	        | UNIT

  fun type_to_string (INT) = "integer"
		| type_to_string (RECORD(fields, uni))= "record"
		| type_to_string (NIL) = "nil"
		| type_to_string (STRING) = "string"
		| type_to_string (ARRAY(t, uni)) = ("array of " ^ (type_to_string t))
    | type_to_string (UNIT) = "unit"
    | type_to_string (NAME(sym, ref r)) = "name"

end
