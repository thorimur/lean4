structure Foo (α : Type) where
  a : α

structure Bar (α : Type) extends Foo α where
  b : a = a

example : Bar Nat := by refine { a := 1, .. }
-- We're checking that the goal is not of the form `{ a := 1 }.a = { a := 1 }.a`.

instance pi.Inhabited {α : Type} {β : α → Type} [∀ x, Inhabited (β x)] : Inhabited (∀ x, β x) :=
by refine { .. }; exact fun _ => default

set_option pp.all true
#print pi.Inhabited
