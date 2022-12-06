-- Check that goals get named appropriately and respect default synthesis
structure Foo where
  x : Nat := 0
  y : Nat

structure Bar extends Foo where
  z : Nat := x

example := by refine { .. : Foo }; case y => exact 0
example := by refine { .. : Bar }; case y => exact 0

-- Check that autoparams fail into named goals when fields are omitted
structure rflFoo where
  x  : Nat
  y  : Nat
  xy : x = y := by rfl

example := by refine { .. : rflFoo }; (case x | y => exact 0); case xy => rfl

-- Check that autoparams work when there are defaults that work
structure autoFoo where
  x  : Nat := 0
  y  : Nat := 0
  xy : x = y := by rfl

example := { .. : autoFoo }

-- Check that autoparams fail into named goals when there are defaults
structure nonAutoFoo where
  x  : Nat := 0
  y  : Nat := 0
  xy : x = y := by fail

example := by refine { .. : nonAutoFoo }; case xy => rfl

-- Check that name conflict resolution works for two different instances of the same structures
def f0 : Foo → Nat := fun _ => 0
def f1 : Foo → Foo → Unit := fun _ _ => ()

example := by refine { x := f0 { .. }, .. : Foo }; case y | y_1 => exact 0

example := by refine f1 { .. } { .. }; case y | y_1 => exact 0

-- Check that name conflict resolution is aggressive
structure Foo' where
  x : Nat

structure dFoo' where
  x : Nat := 0

def ff' : Foo → Foo' → Unit := fun _ _ => ()
def fdf' : dFoo' → Foo → Unit := fun _ _ => ()

example := by refine ff' { .. } { .. }; case y | x_1 => exact 0
example := by refine fdf' { .. } { .. }; case y => exact 0
