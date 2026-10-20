import FailureOfSemipositiveMetricExtension.RealCurrentDeRham

/-! The de Rham quotient of independent real closed (1,1)-currents, using
arbitrary global distributional one-form primitives rather than potentials. -/
namespace FailureOfSemipositiveMetricExtension.DistributionalCurrent
noncomputable section
open Set
open WeakComplexHessian PshCurvatureCurrentInterface
variable {M A : Type} [TopologicalSpace M] [ChartedSpace Coord M]
variable {D : CoordinateAtlas M A}

def OneCurrent.neg (R : OneCurrent D) : OneCurrent D where
  coefficient a i f := -R.coefficient a i f
  additive a i f g hf hg := by rw [R.additive a i f g hf hg]; ring
  homogeneous a i f hf r := by rw [R.homogeneous a i f hf r]; ring
  finiteOrder a i K hK hKU := by
    obtain ⟨n,B,hB,h⟩ := R.finiteOrder a i K hK hKU
    exact ⟨n,B,hB,fun f hf hfK q hq hbound => by simpa only [norm_neg] using h f hf hfK q hq hbound⟩
  transported_test := R.transported_test
  compatible a b f hf i := by simp only [R.compatible a b f hf i,Finset.sum_neg_distrib]

def OneCurrent.add (R S : OneCurrent D) : OneCurrent D where
  coefficient a i f := R.coefficient a i f + S.coefficient a i f
  additive a i f g hf hg := by rw [R.additive a i f g hf hg,S.additive a i f g hf hg]; ring
  homogeneous a i f hf r := by rw [R.homogeneous a i f hf r,S.homogeneous a i f hf r]; ring
  finiteOrder a i K hK hKU := by
    obtain ⟨n,B,hB,h⟩ := R.finiteOrder a i K hK hKU
    obtain ⟨m,C,hC,k⟩ := S.finiteOrder a i K hK hKU
    refine ⟨max n m,B+C,add_nonneg hB hC,?_⟩
    intro f hf hfK q hq hbound
    exact (norm_add_le _ _).trans ((add_le_add
      (h f hf hfK q hq (fun l hl => hbound l (hl.trans (le_max_left _ _))))
      (k f hf hfK q hq (fun l hl => hbound l (hl.trans (le_max_right _ _))))).trans_eq (add_mul _ _ _).symm)
  transported_test := R.transported_test
  compatible a b f hf i := by rw [R.compatible a b f hf i,S.compatible a b f hf i,Finset.sum_add_distrib]

theorem DeRhamExactEquivalent.symm {T S : Current D}
    (h : DeRhamExactEquivalent D T S) : DeRhamExactEquivalent D S T := by
  obtain ⟨R,hR⟩ := h
  refine ⟨R.neg,?_⟩
  intro a f hf i l
  have he := hR a f hf i l
  change _ = -(-R.coefficient a l (firstDirectional (realUnit i) f)) +
    -R.coefficient a i (firstDirectional (realUnit l) f)
  rw [show realTwoCoefficient S.coefficient a i l f - realTwoCoefficient T.coefficient a i l f =
    -(realTwoCoefficient T.coefficient a i l f - realTwoCoefficient S.coefficient a i l f) by ring,he]
  unfold OneCurrent.exteriorCoefficient
  ring

theorem DeRhamExactEquivalent.trans {T S Q : Current D}
    (hTS : DeRhamExactEquivalent D T S) (hSQ : DeRhamExactEquivalent D S Q) :
    DeRhamExactEquivalent D T Q := by
  obtain ⟨R,hR⟩ := hTS
  obtain ⟨W,hW⟩ := hSQ
  refine ⟨R.add W,?_⟩
  intro a f hf i l
  have h := hR a f hf i l
  have k := hW a f hf i l
  change _ = -(R.coefficient a l (firstDirectional (realUnit i) f) + W.coefficient a l (firstDirectional (realUnit i) f)) +
    (R.coefficient a i (firstDirectional (realUnit l) f) + W.coefficient a i (firstDirectional (realUnit l) f))
  unfold OneCurrent.exteriorCoefficient at h k
  linarith

/-- Equality is included explicitly, so no theorem about smoothness of transported
zero-form tests is hidden in the construction of a zero primitive. -/
def DeRhamCohomologous (D : CoordinateAtlas M A) (T S : Current D) : Prop :=
  T = S ∨ DeRhamExactEquivalent D T S

theorem DeRhamCohomologous.refl (T : Current D) : DeRhamCohomologous D T T := Or.inl rfl

theorem DeRhamCohomologous.symm {T S : Current D} (h : DeRhamCohomologous D T S) :
    DeRhamCohomologous D S T := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem DeRhamCohomologous.trans {T S Q : Current D}
    (h : DeRhamCohomologous D T S) (k : DeRhamCohomologous D S Q) :
    DeRhamCohomologous D T Q := by
  rcases h with rfl | h
  · exact k
  rcases k with rfl | k
  · exact Or.inr h
  · exact Or.inr (h.trans k)

def deRhamSetoid (D : CoordinateAtlas M A) : Setoid (Current D) where
  r := DeRhamCohomologous D
  iseqv := ⟨DeRhamCohomologous.refl,fun h => h.symm,fun h k => h.trans k⟩

def DeRhamCurrentClass (D : CoordinateAtlas M A) := Quotient (deRhamSetoid D)
def deRhamClass {D : CoordinateAtlas M A} (T : Current D) : DeRhamCurrentClass D := Quotient.mk _ T

theorem deRhamClass_eq_iff (T S : Current D) :
    deRhamClass T = deRhamClass S ↔ DeRhamCohomologous D T S := Quotient.eq

end
end FailureOfSemipositiveMetricExtension.DistributionalCurrent
