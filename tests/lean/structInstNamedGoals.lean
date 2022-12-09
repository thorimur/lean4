-- Check that goals get named appropriately and respect default synthesis
structure Foo where
  x : Nat := 0
  y : Nat

structure Bar extends Foo where
  z : Nat := x

example := by refine { .. : Foo }; case y => exact 0
example := by refine { .. : Bar }; case y => exact 0
