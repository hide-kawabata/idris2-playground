-- Adam Chlipara, Certified Programming with Dependent Types
-- Chapter 2

-- 2.1.1 Source Language

data BinopT : Type where
    Plus : BinopT
    Times : BinopT

data Exp : Type where
    Const : Nat -> Exp
    Binop : BinopT -> Exp -> Exp -> Exp

binopDenote : (b : BinopT) -> Nat -> Nat -> Nat
binopDenote Plus = \x, y => x + y
binopDenote Times = \x, y => x * y

expDenote : (e : Exp) -> Nat
expDenote (Const n) = n
expDenote (Binop b e1 e2) = (binopDenote b) (expDenote e1) (expDenote e2)

t01 : expDenote (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)) = 28
t01 = Refl

-- 2.1.2 Target Language

data Instr : Type where
    IConst : Nat -> Instr
    IBinop : BinopT -> Instr

Prog : Type
Prog = List Instr

Stack : Type
Stack = List Nat

instrDenote : (i : Instr) -> (s : Stack) -> Maybe Stack
instrDenote (IConst n) s = Just (n :: s)
instrDenote (IBinop b) [] = Nothing
instrDenote (IBinop b) (x :: []) = Nothing
instrDenote (IBinop b) (arg1 :: (arg2 :: s')) = Just ((binopDenote b) arg1 arg2 :: s')

progDenote : (p : Prog) -> (s : Stack) -> Maybe Stack
progDenote [] s = Just s
progDenote (i :: p') s =
    case instrDenote i s of
        Nothing => Nothing
        (Just s') => progDenote p' s'

-- 2.1.3 Translation

compile : (e : Exp) -> Prog
compile (Const n) = IConst n :: []
compile (Binop b e1 e2) =
    compile e2 ++ compile e1 ++ IBinop b :: []

t02 : compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)) =
    IConst 7 :: IConst 2 :: IConst 2 :: IBinop Plus :: IBinop Times :: []
t02 = Refl
t03 : progDenote (compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7))) [] =
    Just (28 :: [])
t03 = Refl

-- 2.1.4 Translation Correctness

compileCorrect : (e : Exp) -> progDenote (compile e) [] = Just (expDenote e :: [])
compileCorrect (Const n) = Refl
compileCorrect (Binop b e1 e2) = ?compileCorrect_rhs_1

lnm : {0 a : Type} -> (l1, l2, l3 : List a) ->
    l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3
lnm [] l2 l3 = Refl
lnm (x :: xs) l2 l3 = cong (x::) (lnm xs l2 l3)
{-
lnm : {0 a : Type} -> {l1, l2, l3 : List a} ->
    l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3
lnm {l1 = []} {l2} {l3} = Refl
lnm {l1 = (x :: xs)} {l2} {l3} = cong (x ::) lnm
 -}

compileCorrect' : (e : Exp) -> (p : Prog) -> (s : Stack) ->
    progDenote (compile e ++ p) s = progDenote p (expDenote e :: s)
compileCorrect' (Const n) p s = Refl
compileCorrect' (Binop b e1 e2) p s =
-- goal: progDenote ((compile e2 ++ (compile e1 ++ [IBinop b])) ++ p) s =
--        progDenote p (binopDenote b (expDenote e1) (expDenote e2) :: s)
    let ih1 = compileCorrect' e1 in
    let ih2 = compileCorrect' e2 in
    -- let r = lnm {l1=(compile e2)} {l2=(compile e1 ++ [IBinop b])} {l3=p} in
    let r = lnm (compile e2) (compile e1 ++ [IBinop b]) p in
    rewrite sym r in
    rewrite ih2 ((compile e1 ++ [IBinop b]) ++ p) s in
    -- let r' = lnm {l1=compile e1} {l2=[IBinop b]} {l3=p} in
    let r' = lnm (compile e1) [IBinop b] p in
    rewrite sym r' in
    rewrite ih1 (IBinop b :: p) (expDenote e2 :: s) in
    Refl
