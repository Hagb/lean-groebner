
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

instance : Add (TermOrder α) := α_add
instance : Zero (TermOrder α) := α_zero
instance : AddCancelCommMonoid (TermOrder α)
  := α_add_cancel_comm_monoid
instance : Inhabited (TermOrder α) := α_inhabited

instance
  [LinearOrder (TermOrder α)]
  [CovariantClass (TermOrder α) (TermOrder α) (·+·) (·≤·)]
  [IsWellOrder (TermOrder α) (·<·)] :
  WellFoundedRelation (TermOrder α) := IsWellOrder.toHasWellFounded
instance
  [LinearOrder (TermOrder α)]
  [IsWellOrder (TermOrder α) (·<·)] :
  WellFoundedRelation (WithBot (TermOrder α)) :=
    IsWellOrder.toHasWellFounded

instance {α : Type _}
  [AddCancelCommMonoid (TermOrder α)] [LinearOrder (TermOrder α)]
  [CovariantClass (TermOrder α) (TermOrder α) (·+·) (·≤·)] :
  LinearOrderedAddCommMonoid (TermOrder α) :=
{
  add_le_add_left := by
    intros a b hab c
    simp only [add_le_add_iff_left, hab]
}
end TermOrder


-- @[simp]
-- lemma zero_le''' (a : α): 0 ≤ a := 
-- example [Zero α] [LE α] [ZeroLEClass α] : Bot α := inferInstance
-- from https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.E2.9C.94.20Override.20default.20ordering.20instance/near/339882298

variable {β :Type _}

class ZeroLEClass (β: Type _) [Zero β] [LE β] where
  zero_le (a: β): 0 ≤ a

instance ZeroLEClass.toOrderBot [Zero β] [LE β] [ZeroLEClass β]: OrderBot β :=
  {
    bot := 0
    bot_le := by
      intro a
      apply zero_le
  }

@[simp]
lemma zero_le''' [Zero β] [LE β] [ZeroLEClass β] (a: β) : 0 ≤ a :=
  ZeroLEClass.zero_le a

variable [AddCancelCommMonoid β]
variable [LinearOrder β] [ZeroLEClass β] [IsWellOrder β (·<·)]
variable [CovariantClass β β (·+·) (·≤·)]

class TermOrderClass (β : Type _) [AddCancelCommMonoid β]
  extends LinearOrder β,
          ZeroLEClass β,
          IsWellOrder β (·<·),
          CovariantClass β β (·+·) (·≤·)


lemma TermOrder.le_of_finsupp_le (h: k₁≤k₂): LE.le (α:=TermOrder (σ→₀ℕ)) k₁ k₂
  := by  
  rw [←add_tsub_cancel_iff_le.mpr h]  
  -- simp?
  simp only [ge_iff_le, le_add_iff_nonneg_right]
  exact ZeroLEClass.zero_le _

lemma TermOrder.lt_of_finsupp_lt (h: k₁<k₂): LT.lt (α:=TermOrder (σ→₀ℕ)) k₁ k₂  
  := lt_of_le_of_ne (le_of_finsupp_le (le_of_lt h)) (ne_of_lt (α:=σ→₀ℕ) h)


end MvPolynomial
