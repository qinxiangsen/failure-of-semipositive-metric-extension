import FailureOfSemipositiveMetricExtension.CentralTransverseLineAnalytic
import FailureOfSemipositiveMetricExtension.GenericConicRestrictionFactors

/-! Exact degree-one,degree-one,degree-one,degree-zero transition comparison. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff BigOperators

abbrev Frame := FixedFiberBundle.Index

def restrictionDegree (a : ℤ) (b : Fin 4 → ℤ) : ℤ := a + b 0 + b 1 + b 2

def restrictionPatch (c : Data) (e : Fin 2) (i : Frame) : Set Direction :=
  ProjectiveLine.chartSet e ∩ param c ⁻¹' FixedFiberBundle.baseSet 0 i

def restrictionFactor (c : Data) (a : ℤ) (b : Fin 4 → ℤ) (e : Fin 2) (i : Frame)
    (d : Direction) : ℂ :=
  baseVector c (ProjectiveLine.normalizedVector e d) i.1 ^ a *
    ∏ r, directionVector c r (ProjectiveLine.normalizedVector e d) (i.2 r) ^ b r

theorem base_normalizedVector (c : Data) (e : Fin 2) (d : Direction)
    (hd : d ∈ ProjectiveLine.chartSet e) :
    base c d = ProjectivePlane.vectorPoint (baseVector c (ProjectiveLine.normalizedVector e d)) := by
  rw [← ProjectiveLine.param_coordinates e d hd,base_param]
  simp only [ProjectiveLine.normalizedVector,ProjectiveLine.coordinates_param]

theorem direction_normalizedVector (c : Data) (r : Fin 4) (e : Fin 2) (d : Direction)
    (hd : d ∈ ProjectiveLine.chartSet e) :
    direction c r d = ProjectiveLine.vectorPoint (directionVector c r (ProjectiveLine.normalizedVector e d)) := by
  rw [← ProjectiveLine.param_coordinates e d hd,direction_param]
  simp only [ProjectiveLine.normalizedVector,ProjectiveLine.coordinates_param]

theorem restrictionPatch_isOpen (c : Data) (e : Fin 2) (i : Frame) :
    IsOpen (restrictionPatch c e i) :=
  (ProjectiveLine.chartSet_isOpen e).inter
    ((FixedFiberBundle.baseSet_isOpen 0 i).preimage (param_contMDiff c 0).continuous)

theorem restrictionPatch_cover (c : Data) (d : Direction) :
    ∃ e i, d ∈ restrictionPatch c e i := by
  exact ⟨(ProjectiveLineBundle.core 0).indexAt d,
    (FixedFiberBundle.core 0 0 (fun _ => 0)).indexAt (param c d),
    (ProjectiveLineBundle.core 0).mem_baseSet_at d,
    (FixedFiberBundle.core 0 0 (fun _ => 0)).mem_baseSet_at (param c d)⟩

theorem restrictionPatch_coordinates (c : Data) (e : Fin 2) (i : Frame) (d : Direction)
    (hd : d ∈ restrictionPatch c e i) :
    baseVector c (ProjectiveLine.normalizedVector e d) i.1 ≠ 0 ∧
      ∀ r, directionVector c r (ProjectiveLine.normalizedVector e d) (i.2 r) ≠ 0 := by
  have h := hd.2
  change base c d ∈ ProjectivePlane.chartSet i.1 ∧
    ∀ r, direction c r d ∈ ProjectiveLine.chartSet (i.2 r) at h
  constructor
  · rw [base_normalizedVector c e d hd.1] at h
    exact (ProjectivePlane.vectorPoint_mem_chartSet_iff _ _
      (baseVector_ne_zero c _ (ProjectiveLine.normalizedVector_ne_zero e d))).mp h.1
  · intro r
    have hr := h.2 r
    rw [direction_normalizedVector c r e d hd.1] at hr
    exact (ProjectiveLine.vectorPoint_mem_chartSet_iff _ _
      (directionVector_ne_zero c r _ (ProjectiveLine.normalizedVector_ne_zero e d))).mp hr

theorem restrictionFactor_ne_zero (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (e : Fin 2) (i : Frame) (d : Direction) (hd : d ∈ restrictionPatch c e i) :
    restrictionFactor c a b e i d ≠ 0 := by
  obtain ⟨hb,hr⟩ := restrictionPatch_coordinates c e i d hd
  exact mul_ne_zero (zpow_ne_zero _ hb) (Finset.prod_ne_zero_iff.mpr (fun r _ => zpow_ne_zero _ (hr r)))

/-- Fixed source normalization: the two ambient frames differ by exactly the
inverse factor dictated by the actual restricted bundle cocycle. -/
theorem restrictionFactor_ambient_change (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (e : Fin 2) (i j : Frame) (d : Direction)
    (hi : d ∈ restrictionPatch c e i) (hj : d ∈ restrictionPatch c e j) :
    restrictionFactor c a b e j d * FixedFiberBundle.gain 0 a b i j (param c d) =
      restrictionFactor c a b e i d := by
  obtain ⟨hbi,hri⟩ := restrictionPatch_coordinates c e i d hi
  obtain ⟨hbj,hrj⟩ := restrictionPatch_coordinates c e j d hj
  change _ * (ProjectivePlaneBundle.gain a i.1 j.1 (base c d) *
    ∏ r,ProjectiveLineBundle.gain (b r) (i.2 r) (j.2 r) (direction c r d)) = _
  simp only [ProjectivePlaneBundle.gain,ProjectiveLineBundle.gain]
  rw [base_normalizedVector c e d hi.1,ProjectivePlane.bundle_ratio_vectorPoint _ _ _ hbj]
  have hrat : ∀ r, ProjectiveLineBundle.ratio (i.2 r) (j.2 r) (direction c r d) =
      directionVector c r (ProjectiveLine.normalizedVector e d) (i.2 r) /
        directionVector c r (ProjectiveLine.normalizedVector e d) (j.2 r) := by
    intro r
    rw [direction_normalizedVector c r e d hi.1]
    exact ProjectiveLine.bundle_ratio_vectorPoint _ _ _ (hri r) (hrj r)
  simp_rw [hrat]
  unfold restrictionFactor
  rw [show ∀ A B C D : ℂ, (A*B)*(C*D) = (A*C)*(B*D) from by intros; ring]
  congr 1
  · rw [← mul_zpow,mul_div_cancel₀ _ hbj]
  · rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro r _
    rw [← mul_zpow,mul_div_cancel₀ _ (hrj r)]

/-- Changing the normalized parameter multiplies the factor by the exact
homogeneous degree, with integer powers including negative degrees. -/
theorem restrictionFactor_source_change (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (e f : Fin 2) (i : Frame) (d : Direction)
    (he : d ∈ ProjectiveLine.chartSet e) (hf : d ∈ ProjectiveLine.chartSet f) :
    restrictionFactor c a b f i d =
      ProjectiveLineBundle.gain (restrictionDegree a b) e f d * restrictionFactor c a b e i d := by
  let R := ProjectiveLineBundle.ratio e f d
  have hR : R ≠ 0 := ProjectiveLineBundle.ratio_ne_zero e f d he hf
  unfold restrictionFactor
  rw [ProjectiveLine.normalizedVector_change e f d he hf,baseVector_smul]
  simp only [Fin.prod_univ_four,directionVector,show (0:Fin 4) ≠ 3 by decide,
    show (1:Fin 4) ≠ 3 by decide,show (2:Fin 4) ≠ 3 by decide,if_false,if_true,
    map_smul,Pi.smul_apply,smul_eq_mul,mul_zpow]
  change (R^a * _) * ((R^(b 0)*_) * (R^(b 1)*_) * (R^(b 2)*_) * _) =
    R^(a+b 0+b 1+b 2) * _
  simp only [zpow_add₀ hR]
  ring

/-- Exact two-sided cocycle identity on the actual refined cover. -/
theorem restrictionFactor_change (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (e f : Fin 2) (i j : Frame) (d : Direction)
    (hi : d ∈ restrictionPatch c e i) (hj : d ∈ restrictionPatch c f j) :
    restrictionFactor c a b f j d * FixedFiberBundle.gain 0 a b i j (param c d) =
      ProjectiveLineBundle.gain (restrictionDegree a b) e f d * restrictionFactor c a b e i d := by
  rw [restrictionFactor_source_change c a b e f j d hi.1 hj.1,mul_assoc,
    restrictionFactor_ambient_change c a b e i j d hi ⟨hi.1,hj.2⟩]

theorem restrictionFactor_contMDiffOn (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (e : Fin 2) (i : Frame) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) n (restrictionFactor c a b e i) (restrictionPatch c e i) := by
  have hv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ,Blowup.Plane) n (ProjectiveLine.normalizedVector e)
      (restrictionPatch c e i) :=
    (ProjectiveLine.sourceVector_contDiff e n).contMDiff.comp_contMDiffOn
      ((ProjectiveLineBundle.coordinates_contMDiffOn e n).mono inter_subset_left)
  have hb : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) n
      (fun d => baseVector c (ProjectiveLine.normalizedVector e d) i.1) (restrictionPatch c e i) :=
    (contDiff_apply ℂ ℂ i.1).contMDiff.comp_contMDiffOn
      ((baseVector_contDiff c n).contMDiff.comp_contMDiffOn hv)
  have hr (r : Fin 4) : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) n
      (fun d => directionVector c r (ProjectiveLine.normalizedVector e d) (i.2 r))
      (restrictionPatch c e i) :=
    (contDiff_apply ℂ ℂ (i.2 r)).contMDiff.comp_contMDiffOn
      ((directionVector_contDiff c r n).contMDiff.comp_contMDiffOn hv)
  have hbp := (ProjectiveLineBundle.scalar_zpow_contDiffOn a n).contMDiffOn.comp hb
    (fun d hd => (restrictionPatch_coordinates c e i d hd).1)
  have hrp (r : Fin 4) := (ProjectiveLineBundle.scalar_zpow_contDiffOn (b r) n).contMDiffOn.comp (hr r)
    (fun d hd => (restrictionPatch_coordinates c e i d hd).2 r)
  unfold restrictionFactor
  simpa only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,
    smul_eq_mul,Function.comp_apply] using hbp.smul ((hrp 0).smul ((hrp 1).smul ((hrp 2).smul (hrp 3))))

theorem restrictionFactor_inv_contMDiffOn (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (e : Fin 2) (i : Frame) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) n (fun d => (restrictionFactor c a b e i d)⁻¹)
      (restrictionPatch c e i) := by
  have h : ContDiffOn ℂ n (fun z : ℂ => z⁻¹) {z | z ≠ 0} := contDiffOn_id.inv (fun _ h => h)
  exact h.contMDiffOn.comp (restrictionFactor_contMDiffOn c a b e i n)
    (fun d hd => restrictionFactor_ne_zero c a b e i d hd)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine
