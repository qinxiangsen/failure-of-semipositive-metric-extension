import FailureOfSemipositiveMetricExtension.GlobalFiberSections

/-! Analytic section gluing on the actual fixed-fibre manifold and pulled-back bundles. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped Manifold ContDiff Topology

structure LocalSectionData (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (U : Set (Fiber t)) where
  coefficient : Index → Fiber t → ℂ
  analytic : ∀ i, ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (coefficient i) (U ∩ baseSet t i)
  compatible : ∀ i j p, p ∈ U → p ∈ baseSet t i ∩ baseSet t j →
    gain t a b i j p * coefficient i p = coefficient j p

/-- A scalar analytic function in one actual trivialization defines a local bundle section. -/
def localSectionOfTrivialization (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (U : Set (Fiber t)) (j : Index)
    (hU : U ⊆ baseSet t j) (f : Fiber t → ℂ)
    (hf : ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω f U) : LocalSectionData t a b U where
  coefficient i p := gain t a b j i p * f p
  analytic i := by
    have hg := (gain_contMDiffOn t a b j i ω).mono
      (show U ∩ baseSet t i ⊆ baseSet t j ∩ baseSet t i from fun _ hp => ⟨hU hp.1,hp.2⟩)
    exact hg.smul (hf.mono inter_subset_left)
  compatible i k p hp hik := by
    rw [← mul_assoc,gain_comp t a b j i k p ⟨⟨hU hp,hik.1⟩,hik.2⟩]

/-- Gluing analytic local sections requires equality on every actual overlap.
No geometric existence statement is assumed here. -/
def glueSections {K : Type*} (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (U : K → Set (Fiber t))
    (hopen : ∀ k, IsOpen (U k)) (hcover : ∀ p, ∃ k, p ∈ U k)
    (s : ∀ k, LocalSectionData t a b (U k))
    (hcompat : ∀ k l i p, p ∈ U k → p ∈ U l → p ∈ baseSet t i →
      (s k).coefficient i p = (s l).coefficient i p) : SectionData t a b where
  coefficient i p := (s (Classical.choose (hcover p))).coefficient i p
  analytic i := by
    intro p hp
    let k := Classical.choose (hcover p)
    have hpk : p ∈ U k := Classical.choose_spec (hcover p)
    have hnb : U k ∩ baseSet t i ∈ 𝓝 p :=
      ((hopen k).inter (baseSet_isOpen t i)).mem_nhds ⟨hpk,hp⟩
    have ha := ((s k).analytic i).contMDiffAt hnb
    apply ContMDiffAt.contMDiffWithinAt
    apply ha.congr_of_eventuallyEq
    filter_upwards [hnb] with q hq
    exact hcompat (Classical.choose (hcover q)) k i q
      (Classical.choose_spec (hcover q)) hq.1 hq.2
  compatible i j p hp := (s (Classical.choose (hcover p))).compatible i j p
    (Classical.choose_spec (hcover p)) hp

theorem glueSections_coefficient {K : Type*} (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (U : K → Set (Fiber t))
    (hopen : ∀ k, IsOpen (U k)) (hcover : ∀ p, ∃ k, p ∈ U k)
    (s : ∀ k, LocalSectionData t a b (U k))
    (hcompat : ∀ k l i p, p ∈ U k → p ∈ U l → p ∈ baseSet t i →
      (s k).coefficient i p = (s l).coefficient i p)
    (k : K) (i : Index) (p : Fiber t) (hp : p ∈ U k) (hi : p ∈ baseSet t i) :
    (glueSections t a b U hopen hcover s hcompat).coefficient i p = (s k).coefficient i p :=
  hcompat _ k i p (Classical.choose_spec (hcover p)) hp hi
end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
