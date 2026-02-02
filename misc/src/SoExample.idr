-- Source - https://stackoverflow.com/questions/72114989/how-can-i-convince-idris-that-my-function-is-covering
-- Posted by Nicolas, modified by community. See post 'Timeline' for change history
-- Retrieved 2026-01-27, License - CC BY-SA 4.0

import Data.So

doSomething : (c : Char) -> {auto isPar : So (c == '(' || c == ')')} -> Int
doSomething x {isPar} = case (choose (x == '(')) of
  Left _ => 1
  Right notOpen => case (choose (x == ')')) of
    Left _ => -1
    Right notClose => case (soOr isPar) of -- analyse the reason why isPar is true (i.e., the cause of contradiction)
        Left isOpen => let p = soNotToNotSo notOpen in let contra = p isOpen in absurd contra
        Right isClose => absurd $ (soNotToNotSo notClose) isClose
    -- Right notClose => case (soOr isPar) of
    --     Left isOpen => absurd $ soNotToNotSo notOpen isOpen
    --     Right isClose => absurd $ soNotToNotSo notClose isClose
