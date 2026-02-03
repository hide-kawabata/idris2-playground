-- 14. The Truth about Interfaces
-- Internally, an interface is just a record data type, with its fields corresponding to the members of the interface. An interface implementation is a value of such a record, annotated with a %hint pragma (see below) to make the value available during proof search. Finally, a constrained function is just a function with one or more auto implicit arguments.

isElem1 : Eq a => a -> List a -> Bool
isElem1 v []        = False
isElem1 v (x :: xs) = x == v || isElem1 v xs

isElem2 : {auto _ : Eq a} -> a -> List a -> Bool
isElem2 v []        = False
isElem2 v (x :: xs) = x == v || isElem2 v xs

eq : {auto i : Eq a} -> a -> a -> Bool
eq {i = MkEq feq fneq} = feq

-----------------

record Print a where
  constructor MkPrint
  print' : a -> String

print : Print a => a -> String
print = print' %search

print2 : (impl : Print a) => a -> String
print2 = print' impl

print3 : {auto impl : Print a} -> a -> String
print3 = print' impl

-- Whenever we write {auto x : Foo} -> we can just as well write (x : Foo) => and vice versa.

%hint
listPrint : Print (List a)
listPrint = MkPrint $ \e => "Length of the list: \{show $ length e}"
-- print3 (the (List Nat) [1,2]) or print3 [1,2]
