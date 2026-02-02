import Data.Nat
import Syntax.PreorderReasoning
-- multThree : (a, b, c : Nat) -> a * b * c = c * a * b
-- multThree a b c =
--   (a * b * c)       ={ sym (multAssociative a b c) }=
--   (a * (b * c))     ={ cong (multCommutative b c) }=
--   (a * (c * b))     ={ multAssociative a c b }=
--   (a * c * b)       ={ cong {f = (* b)} (multCommutative a c) }=
--   (c * a * b)       QED

t : 3 = 3
t = Calc $ 
    |~ 3

multThree : (a, b, c : Nat) -> a * b * c = c * a * b
multThree a b c = Calc $
    |~ a * b * c
    ~~ a * (b * c) ... sym (multAssociative a b c)
    ~~ a * (c * b) ... cong (a*) (multCommutative b c)
    ~~ a * c * b ... multAssociative a c b
    ~~ c * a * b ... cong (*b) (multCommutative a c)
    -- ~~ c * a * b ... Refl

multThree' : (a, b, c : Nat) -> a * b * c = c * a * b
multThree' a b c = Calc $
    |~ a * b * c
    ~~ a * (b * c) ..> sym (multAssociative a b c)
    ~~ a * (c * b) ..> cong (a*) (multCommutative b c)
    ~~ a * c * b ..> multAssociative a c b
    ~~ c * a * b ..> cong (*b) (multCommutative a c)
    -- ~~ c * a * b ... Refl

-- l1: (a : Integer) -> a < a + 1 = True
-- l1 a = Calc $ |~ a
    -- ~~ ?hole

