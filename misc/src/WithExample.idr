||| Test if a Char is an open or close paren.
isParen : Char -> Bool
isParen '(' = True
isParen ')' = True
isParen _ = False

||| Obtain the integer code corresponding to a paren.
||| Proof is required that c is '(' or ')'.
parenCode : (c : Char) -> {auto 0 prf_isParen : isParen c === True} -> Integer
parenCode c with (isParen c)
  parenCode '(' | True = 1
  parenCode ')' | True = -1
--   parenCode c | False = ?parenCode_rhs_rhss_0
--   parenCode _ | _ = ?parenCode_rhs_rhss_3
  parenCode c | True = ?parenCode_rhs_rhss_3
  parenCode _ | False impossible

-- parenCode c with (isParen c)
--   parenCode '(' | True = 1
--   parenCode ')' | True = -1
--   parenCode _   | False impossible