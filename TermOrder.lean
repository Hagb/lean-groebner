
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.MvPolynomial.Basic
namespace MvPolynomial
-- refer to https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Order/Synonym.lean

variable {α : Type _}

/-- A type synonym to equip a type with its term_ordericographic order. -/
def TermOrder (α : Type _) :=
  α

/-- `toTermOrder` is the identity function to the `TermOrder` of a type.  -/
@[match_pattern]
def toTermOrder : α ≃ TermOrder α :=
  Equiv.refl _

/-- `ofTermOrder` is the identity function from the `TermOrder` of a type.  -/
@[match_pattern]
def ofTermOrder : TermOrder α ≃ α :=
  Equiv.refl _

@[simp]
theorem toTermOrder_symm_eq : (@toTermOrder α).symm = ofTermOrder :=
  rfl

@[simp]
theorem ofTermOrder_symm_eq : (@ofTermOrder α).symm = toTermOrder :=
  rfl

@[simp]
theorem toTermOrder_ofTermOrder (a : TermOrder α) : toTermOrder (ofTermOrder a) = a :=
  rfl

@[simp]
theorem ofTermOrder_toTermOrder (a : α) : ofTermOrder (toTermOrder a) = a :=
  rfl

-- Porting note:
-- removed @[simp] since this already follows by `simp only [EmbeddingLike.apply_eq_iff_eq]`
theorem toTermOrder_inj {a b : α} : toTermOrder a = toTermOrder b ↔ a = b :=
  Iff.rfl

-- Porting note:
-- removed @[simp] since this already follows by `simp only [EmbeddingLike.apply_eq_iff_eq]`
theorem ofTermOrder_inj {a b : TermOrder α} : ofTermOrder a = ofTermOrder b ↔ a = b :=
  Iff.rfl

/-- A recursor for `TermOrder`. Use as `induction x using TermOrder.rec`. -/
protected def TermOrder.rec {β : TermOrder α → Sort _} (h : ∀ a, β (toTermOrder a)) :
  ∀ a, β a := fun a => h (ofTermOrder a)
-- #align term_order.rec TermOrder.rec
namespace TermOrder
variable [α_add: Add α] [α_zero: Zero α]
variable [α_add_cancel_comm_monoid: AddCancelCommMonoid α]
variable [α_inhabited: Inhabited α]

instance add: Add (TermOrder α) := α_add
instance zero: Zero (TermOrder α) := α_zero
instance toAddCancelCommMonoid: AddCancelCommMonoid (TermOrder α)
  := α_add_cancel_comm_monoid
instance toAddCommMonoid: AddCommMonoid (TermOrder α)
  := α_add_cancel_comm_monoid.toAddCommMonoid

instance: Inhabited (TermOrder α) := α_inhabited
end TermOrder

class ZeroLEClass (α: Type _) [Zero α] [LE α] where
  zero_le (a: α): 0 ≤ a

instance ZeroLEClass.toOrderBot [Zero α] [LE α] [ZeroLEClass α]: OrderBot α :=
  {
    bot := 0
    bot_le := by
      intro a
      apply zero_le
  }

-- from https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.E2.9C.94.20Override.20default.20ordering.20instance/near/339882298
class TermOrderClass (α : Type _) [AddCancelCommMonoid α]
  extends LinearOrder α,
          ZeroLEClass α,
          IsWellOrder α (·<·),
          CovariantClass α α (·+·) (·≤·)

variable [AddCancelCommMonoid α]
variable [term_order_class: TermOrderClass α]

-- instance TermOrder.toOrderBot: OrderBot α := 

instance:
  CovariantClass α α (·+·) (·≤·) := TermOrderClass.toCovariantClass

instance:
  ContravariantClass α α (·+·) (·<·) :=
    contravariant_add_lt_of_covariant_add_le α

instance:
  CovariantClass α α (·+·) (·<·) :=
    AddLeftCancelSemigroup.covariant_add_lt_of_covariant_add_le (N:=α)

instance: LinearOrderedAddCommMonoid α := {
  add_le_add_left := by
    intros a b hab c
    simp only [add_le_add_iff_left, hab]
}

-- @[default_instance]
instance TermOrder.isWellFoundedRelation: WellFoundedRelation α :=
  term_order_class.toWellFoundedRelation

variable {σ: Type _} [TermOrderClass (TermOrder (σ→₀ℕ))] {k₁ k₂: σ→₀ℕ}

lemma TermOrder.le_of_finsupp_le (h: k₁≤k₂): LE.le (α:=TermOrder (σ→₀ℕ)) k₁ k₂
  := by
  rw [←add_tsub_cancel_iff_le.mpr h]
  -- simp?
  simp only [ge_iff_le, le_add_iff_nonneg_right]
  exact ZeroLEClass.zero_le _
lemma TermOrder.lt_of_finsupp_lt (h: k₁<k₂): LT.lt (α:=TermOrder (σ→₀ℕ)) k₁ k₂
  := lt_of_le_of_ne (le_of_finsupp_le (le_of_lt h)) (ne_of_lt (α:=σ→₀ℕ) h)


end MvPolynomial