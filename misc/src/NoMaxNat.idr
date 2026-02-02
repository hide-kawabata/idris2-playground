import Data.Nat
noMaxNat : (n : Nat) -> DPair Nat (\m => GT m n)
noMaxNat 0 = MkDPair (S 0) (LTESucc LTEZero)
noMaxNat (S k) = 
    let MkDPair (S k) prf = noMaxNat k in
    MkDPair (S (S k)) (LTESucc prf)