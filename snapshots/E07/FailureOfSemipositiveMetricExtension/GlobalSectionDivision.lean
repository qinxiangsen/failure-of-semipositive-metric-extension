import FailureOfSemipositiveMetricExtension.GlobalSectionGluing
import FailureOfSemipositiveMetricExtension.GlobalSectionProducts

/-! Actual analytic section division from verified regular local quotients.
All density, overlap and regularity requirements are explicit and proved below. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set Bundle IsManifold FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped Manifold ContDiff

theorem localDivision_identity {a c : ℤ} {b d : Fin 4 → ℤ}
    (D : SectionData c d) (N : SectionData (a+c) (fun r => b r+d r))
    (U : Set Total) (j : Index) (hU : U ⊆ baseSet j) (f : Total → ℂ)
    (hf : ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω f U)
    (hdiv : ∀ p ∈ U, f p * D.coefficient j p = N.coefficient j p)
    (i : Index) (p : Total) (hp : p ∈ U) (hi : p ∈ baseSet i) :
    (localSectionOfTrivialization a b U j hU f hf).coefficient i p * D.coefficient i p =
      N.coefficient i p := by
  have hj := hU hp
  have hD := D.compatible j i p ⟨hj,hi⟩
  have hN := N.compatible j i p ⟨hj,hi⟩
  change (gain a b j i p * f p) * D.coefficient i p = _
  rw [← hD]
  calc
    (gain a b j i p * f p) * (gain c d j i p * D.coefficient j p) =
        (gain a b j i p * gain c d j i p) * (f p * D.coefficient j p) := by ring
    _ = gain (a+c) (fun r => b r+d r) j i p * N.coefficient j p := by
      rw [← gain_add a c b d j i p ⟨hj,hi⟩,hdiv p hp]
    _ = N.coefficient i p := hN

theorem localDivision_compatible {a c : ℤ} {b d : Fin 4 → ℤ}
    (D : SectionData c d) (N : SectionData (a+c) (fun r => b r+d r))
    (Z : Set Total) (hZ : Dense Z)
    (hD : ∀ p ∈ Z, ∀ i, p ∈ baseSet i → D.coefficient i p ≠ 0)
    (U V : Set Total) (hU : IsOpen U) (hV : IsOpen V)
    (s : LocalSectionData a b U) (t : LocalSectionData a b V)
    (hs : ∀ i p, p ∈ U → p ∈ baseSet i → s.coefficient i p * D.coefficient i p = N.coefficient i p)
    (ht : ∀ i p, p ∈ V → p ∈ baseSet i → t.coefficient i p * D.coefficient i p = N.coefficient i p)
    (i : Index) (p : Total) (hpU : p ∈ U) (hpV : p ∈ V) (hpi : p ∈ baseSet i) :
    s.coefficient i p = t.coefficient i p := by
  let W := U ∩ V ∩ baseSet i
  have hW : IsOpen W := (hU.inter hV).inter (baseSet_isOpen i)
  have he : EqOn (s.coefficient i) (t.coefficient i) (W ∩ Z) := by
    intro q hq
    apply mul_right_cancel₀ (hD q hq.2 i hq.1.2)
    exact (hs i q hq.1.1.1 hq.1.2).trans (ht i q hq.1.1.2 hq.1.2).symm
  have hext := he.of_subset_closure
    (((s.analytic i).continuousOn).mono (show W ⊆ U ∩ baseSet i from fun _ h => ⟨h.1.1,h.2⟩))
    (((t.analytic i).continuousOn).mono (show W ⊆ V ∩ baseSet i from fun _ h => ⟨h.1.2,h.2⟩))
    inter_subset_left (hZ.open_subset_closure_inter hW)
  exact hext ⟨⟨hpU,hpV⟩,hpi⟩

/-- Verified regular local quotients glue to a genuine analytic quotient section. -/
def divideSections {K : Type*} {a c : ℤ} {b d : Fin 4 → ℤ}
    (D : SectionData c d) (N : SectionData (a+c) (fun r => b r+d r))
    (Z : Set Total) (hZ : Dense Z)
    (hD : ∀ p ∈ Z, ∀ i, p ∈ baseSet i → D.coefficient i p ≠ 0)
    (U : K → Set Total) (hopen : ∀ k, IsOpen (U k)) (hcover : ∀ p, ∃ k, p ∈ U k)
    (j : K → Index) (hU : ∀ k, U k ⊆ baseSet (j k))
    (f : K → Total → ℂ)
    (hf : ∀ k, ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω (f k) (U k))
    (hdiv : ∀ k p, p ∈ U k → f k p * D.coefficient (j k) p = N.coefficient (j k) p) :
    SectionData a b :=
  glueSections a b U hopen hcover
    (fun k => localSectionOfTrivialization a b (U k) (j k) (hU k) (f k) (hf k))
    (fun k l i p hk hl hi => localDivision_compatible D N Z hZ hD _ _ (hopen k) (hopen l)
      _ _ (fun i p hp hi => localDivision_identity D N _ _ (hU k) _ (hf k) (hdiv k) i p hp hi)
      (fun i p hp hi => localDivision_identity D N _ _ (hU l) _ (hf l) (hdiv l) i p hp hi)
      i p hk hl hi)

theorem divideSections_coefficient {K : Type*} {a c : ℤ} {b d : Fin 4 → ℤ}
    (D : SectionData c d) (N : SectionData (a+c) (fun r => b r+d r))
    (Z : Set Total) (hZ : Dense Z)
    (hD : ∀ p ∈ Z, ∀ i, p ∈ baseSet i → D.coefficient i p ≠ 0)
    (U : K → Set Total) (hopen : ∀ k, IsOpen (U k)) (hcover : ∀ p, ∃ k, p ∈ U k)
    (j : K → Index) (hU : ∀ k, U k ⊆ baseSet (j k))
    (f : K → Total → ℂ)
    (hf : ∀ k, ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω (f k) (U k))
    (hdiv : ∀ k p, p ∈ U k → f k p * D.coefficient (j k) p = N.coefficient (j k) p)
    (k : K) (i : Index) (p : Total) (hp : p ∈ U k) (hi : p ∈ baseSet i) :
    (divideSections D N Z hZ hD U hopen hcover j hU f hf hdiv).coefficient i p =
      gain a b (j k) i p * f k p := by
  unfold divideSections
  exact glueSections_coefficient _ _ _ _ _ _ _ k i p hp hi

end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
