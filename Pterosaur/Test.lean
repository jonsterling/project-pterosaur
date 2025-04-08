axiom A : Type
axiom B : Type
axiom C : Type

class Foo (a : Type) (b : semiOutParam Type) where
  foo : String

instance : Foo A B where
  foo := "AB"

instance : Foo B C where
  foo := "BC"

instance : Foo A C where
  foo := "AC"


instance [Foo x y] [Foo y z] : Foo x z where
  foo := "looped: " ++ @Foo.foo x y _

instance [Foo x y] : Foo x y where
  foo := "looped: " ++ @Foo.foo x y _


#eval @Foo.foo A C _
