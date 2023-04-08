import Mathlib.Data.Finsupp.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Nontrivial
import Mathlib.Order.Basic
import Mathlib.Data.Finsupp.Basic

universe u
-- variable {σ: Type u}
variable {α : Type u}

/-- A type synonym to equip a type with its term_ordericographic order. -/
def TermOrder (α : Type u) :=
  α
#align term_order TermOrder

/-- `toTermOrder` is the identity function to the `TermOrder` of a type.  -/
@[match_pattern]
def toTermOrder : α ≃ TermOrder α :=
  Equiv.refl _
#align to_term_order toTermOrder

/-- `ofTermOrder` is the identity function from the `term_order` of a type.  -/
@[match_pattern]
def ofTermOrder : TermOrder α ≃ α :=
  Equiv.refl _
#align of_term_order ofTermOrder

@[simp]
theorem toTermOrder_symm_eq : (@toTermOrder α).symm = ofTermOrder :=
  rfl
#align to_term_order_symm_eq toTermOrder_symm_eq

@[simp]
theorem ofTermOrder_symm_eq : (@ofTermOrder α).symm = toTermOrder :=
  rfl
#align of_term_order_symm_eq ofTermOrder_symm_eq

@[simp]
theorem toTermOrder_ofTermOrder (a : TermOrder α) : toTermOrder (ofTermOrder a) = a :=
  rfl
#align to_term_order_of_term_order toTermOrder_ofTermOrder

@[simp]
theorem ofTermOrder_toTermOrder (a : α) : ofTermOrder (toTermOrder a) = a :=
  rfl
#align of_term_order_to_term_order ofTermOrder_toTermOrder

-- Porting note:
-- removed @[simp] since this already follows by `simp only [EmbeddingLike.apply_eq_iff_eq]`
theorem toTermOrder_inj {a b : α} : toTermOrder a = toTermOrder b ↔ a = b :=
  Iff.rfl
#align to_term_order_inj toTermOrder_inj

-- Porting note:
-- removed @[simp] since this already follows by `simp only [EmbeddingLike.apply_eq_iff_eq]`
theorem ofTermOrder_inj {a b : TermOrder α} : ofTermOrder a = ofTermOrder b ↔ a = b :=
  Iff.rfl
#align of_term_order_inj ofTermOrder_inj

namespace TermOrder
variable [α_add: Add α] [α_zero: Zero α]
/-- A recursor for `TermOrder`. Use as `induction x using TermOrder.rec`. -/
protected def rec {β : TermOrder α → Sort _} (h : ∀ a, β (toTermOrder a)) : ∀ a, β a := fun a => h (ofTermOrder a)
#align term_order.rec TermOrder.rec

instance add: Add (TermOrder α) := α_add
instance zero: Zero (TermOrder α) := α_zero

variable {σ : Type _}
variable [le': LE (TermOrder (σ →₀ ℕ))]

-- instance lt: LE (TermOrder (σ →₀ ℕ)) := le'

variable (a: TermOrder (σ →₀ ℕ)) (b: TermOrder (σ →₀ ℕ))


noncomputable def test := a+b ≤ a

class TermOrderClass (σ : Type _) [Finite σ] extends LinearOrder (TermOrder (σ →₀ ℕ)) where
  Additive : ∀ v v₁ v₂ : TermOrder (σ →₀ ℕ), v₁ ≤ v₂ → v + v₁ ≤ v + v₂
  zero_le : ∀ v : TermOrder (σ →₀ ℕ), 0 ≤ v
-- #align mv_polynomial.term_order MvPolynomial.TermOrder

#print test
end TermOrder