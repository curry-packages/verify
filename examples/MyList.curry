import Test.Prop

data List a = Empty | Cons a (List a)

append Empty       ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

appendIsAssoc xs ys zs = append (append xs ys) zs -=- append xs (append ys zs)
