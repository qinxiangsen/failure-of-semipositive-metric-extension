import FailureOfSemipositiveMetricExtension.GlobalBundleSections

/-! Analytic section gluing on the actual global manifold and actual bundles. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set Bundle IsManifold FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped Manifold ContDiff Topology

structure LocalSectionData (a : ℤ) (b : Fin 4 → ℤ) (U : Set Total) where
  coefficient : Index → Total → ℂ
  analytic : ∀ i, ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω (coefficient i) (U ∩ baseSet i)
  compatible : ∀ i j p, p ∈ U → p ∈ baseSet i ∩ baseSet j →
    gain a b i j p * coefficient i p = coefficient j p

/-- A scalar analytic function in one actual trivialization defines a local bundle section. -/
def localSectionOfTrivialization (a : ℤ) (b : Fin 4 → ℤ) (U : Set Total) (j : Index)
    (hU : U ⊆ baseSet j) (f : Total → ℂ)
    (hf : ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω f U) : LocalSectionData a b U where
  coefficient i p := gain a b j i p * f p
  analytic i := by
    have hg := (gain_contMDiffOn a b j i ω).mono
      (show U ∩ baseSet i ⊆ baseSet j ∩ baseSet i from fun _ hp => ⟨hU hp.1,hp.2⟩)
    exact hg.smul (hf.mono inter_subset_left)
  compatible i k p hp hik := by
    rw [← mul_assoc,gain_comp a b j i k p ⟨⟨hU hp,hik.1⟩,hik.2⟩]

/-- Gluing analytic local sections requires equality on every actual overlap.
No geometric existence statement is assumed here. -/
def glueSections {K : Type*} (a : ℤ) (b : Fin 4 → ℤ) (U : K → Set Total)
    (hopen : ∀ k, IsOpen (U k)) (hcover : ∀ p, ∃ k, p ∈ U k)
    (s : ∀ k, LocalSectionData a b (U k))
    (hcompat : ∀ k l i p, p ∈ U k → p ∈ U l → p ∈ baseSet i →
      (s k).coefficient i p = (s l).coefficient i p) : SectionData a b where
  coefficient i p := (s (Classical.choose (hcover p))).coefficient i p
  analytic i := by
    intro p hp
    let k := Classical.choose (hcover p)
    have hpk : p ∈ U k := Classical.choose_spec (hcover p)
    have hnb : U k ∩ baseSet i ∈ 𝓝 p :=
      ((hopen k).inter (baseSet_isOpen i)).mem_nhds ⟨hpk,hp⟩
    have ha := ((s k).analytic i).contMDiffAt hnb
    apply ContMDiffAt.contMDiffWithinAt
    apply ha.congr_of_eventuallyEq
    filter_upwards [hnb] with q hq
    exact hcompat (Classical.choose (hcover q)) k i q
      (Classical.choose_spec (hcover q)) hq.1 hq.2
  compatible i j p hp := (s (Classical.choose (hcover p))).compatible i j p
    (Classical.choose_spec (hcover p)) hp

theorem glueSections_coefficient {K : Type*} (a : ℤ) (b : Fin 4 → ℤ) (U : K → Set Total)
    (hopen : ∀ k, IsOpen (U k)) (hcover : ∀ p, ∃ k, p ∈ U k)
    (s : ∀ k, LocalSectionData a b (U k))
    (hcompat : ∀ k l i p, p ∈ U k → p ∈ U l → p ∈ baseSet i →
      (s k).coefficient i p = (s l).coefficient i p)
    (k : K) (i : Index) (p : Total) (hp : p ∈ U k) (hi : p ∈ baseSet i) :
    (glueSections a b U hopen hcover s hcompat).coefficient i p = (s k).coefficient i p :=
  hcompat _ k i p (Classical.choose_spec (hcover p)) hp hi
end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
