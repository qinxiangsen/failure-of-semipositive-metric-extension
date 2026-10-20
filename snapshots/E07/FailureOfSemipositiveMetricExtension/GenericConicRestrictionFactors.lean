import FailureOfSemipositiveMetricExtension.GenericConicAnalytic

/-! Explicit nowhere-zero analytic change-of-frame factors for restricting every
ambient multidegree bundle to the genuine parametrized conic. The exponent is
2a + Σ bᵣ. No degree or intersection-theory assertion is assumed. -/
namespace FailureOfSemipositiveMetricExtension.ProjectivePlane
noncomputable section

theorem bundle_ratio_vectorPoint (i j : Fin 3) (v : Fin 3 → ℂ) (hj : v j ≠ 0) :
    ProjectivePlaneBundle.ratio i j (vectorPoint v) = v i / v j := by
  rw [vectorPoint_eq_param j v hj]
  change vector j (coordinates j (param j (normalize j v))) i = _
  rw [coordinates_param]
  have h := congrFun (vector_normalize j v hj) i
  simp only [Pi.smul_apply,smul_eq_mul] at h
  exact (eq_div_iff hj).mpr (by simpa [mul_comm] using h)

end
end FailureOfSemipositiveMetricExtension.ProjectivePlane

namespace FailureOfSemipositiveMetricExtension.ProjectiveLine
noncomputable section
open Set

def normalizedVector (i : Fin 2) (d : Point) : Blowup.Plane :=
  sourceVector i (coordinates i d)

theorem normalizedVector_ne_zero (i : Fin 2) (d : Point) : normalizedVector i d ≠ 0 :=
  sourceVector_ne_zero i _

theorem vectorPoint_normalizedVector (i : Fin 2) (d : Point) (hd : d ∈ chartSet i) :
    vectorPoint (normalizedVector i d) = d := by
  rw [vectorPoint_eq_mk _ (normalizedVector_ne_zero i d)]
  change Projectivization.mk ℂ (sourceVector i (coordinates i d)) _ = d
  rw [← param_eq_mk_sourceVector]
  exact param_coordinates i d hd

theorem normalizedVector_change (i j : Fin 2) (d : Point)
    (hi : d ∈ chartSet i) (hj : d ∈ chartSet j) :
    normalizedVector j d = ProjectiveLineBundle.ratio i j d • normalizedVector i d := by
  by_cases hij : i = j
  · subst j; simp [ProjectiveLineBundle.ratio_self]
  have h := ProjectiveLineBundle.coordinates_product i j hij d hi hj
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · ext k; fin_cases k
    · simp [normalizedVector,sourceVector,Blowup.vectorX,Blowup.vectorY,ProjectiveLineBundle.ratio]
    · simpa [normalizedVector,sourceVector,Blowup.vectorX,Blowup.vectorY,ProjectiveLineBundle.ratio,mul_comm] using h.symm
  · ext k; fin_cases k
    · simpa [normalizedVector,sourceVector,Blowup.vectorX,Blowup.vectorY,ProjectiveLineBundle.ratio,mul_comm] using h.symm
    · simp [normalizedVector,sourceVector,Blowup.vectorX,Blowup.vectorY,ProjectiveLineBundle.ratio]
  · exact (hij rfl).elim

end
end FailureOfSemipositiveMetricExtension.ProjectiveLine

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff BigOperators

abbrev Frame := FixedFiberBundle.Index

def restrictionDegree (a : ℤ) (b : Fin 4 → ℤ) : ℤ := 2*a + ∑ r, b r

def restrictionPatch (c : Data) (e : Fin 2) (i : Frame) : Set Direction :=
  ProjectiveLine.chartSet e ∩ param c ⁻¹' FixedFiberBundle.baseSet c.t i

def restrictionFactor (c : Data) (a : ℤ) (b : Fin 4 → ℤ) (e : Fin 2) (i : Frame)
    (d : Direction) : ℂ :=
  baseVector c (ProjectiveLine.normalizedVector e d) i.1 ^ a *
    ∏ r, directionMap c r (ProjectiveLine.normalizedVector e d) (i.2 r) ^ b r

theorem base_normalizedVector (c : Data) (e : Fin 2) (d : Direction)
    (hd : d ∈ ProjectiveLine.chartSet e) :
    base c d = ProjectivePlane.vectorPoint (baseVector c (ProjectiveLine.normalizedVector e d)) := by
  rw [← ProjectiveLine.param_coordinates e d hd,base_param]
  simp only [ProjectiveLine.normalizedVector,ProjectiveLine.coordinates_param]

theorem direction_normalizedVector (c : Data) (r : Fin 4) (e : Fin 2) (d : Direction)
    (hd : d ∈ ProjectiveLine.chartSet e) :
    direction c r d = ProjectiveLine.vectorPoint (directionMap c r (ProjectiveLine.normalizedVector e d)) := by
  rw [← ProjectiveLine.param_coordinates e d hd,direction_param]
  simp only [ProjectiveLine.normalizedVector,ProjectiveLine.coordinates_param]

theorem restrictionPatch_isOpen (c : Data) (e : Fin 2) (i : Frame) :
    IsOpen (restrictionPatch c e i) :=
  (ProjectiveLine.chartSet_isOpen e).inter
    ((FixedFiberBundle.baseSet_isOpen c.t i).preimage (param_contMDiff c 0).continuous)

theorem restrictionPatch_cover (c : Data) (d : Direction) :
    ∃ e i, d ∈ restrictionPatch c e i := by
  exact ⟨(ProjectiveLineBundle.core 0).indexAt d,
    (FixedFiberBundle.core c.t 0 (fun _ => 0)).indexAt (param c d),
    (ProjectiveLineBundle.core 0).mem_baseSet_at d,
    (FixedFiberBundle.core c.t 0 (fun _ => 0)).mem_baseSet_at (param c d)⟩

theorem restrictionPatch_coordinates (c : Data) (e : Fin 2) (i : Frame) (d : Direction)
    (hd : d ∈ restrictionPatch c e i) :
    baseVector c (ProjectiveLine.normalizedVector e d) i.1 ≠ 0 ∧
      ∀ r, directionMap c r (ProjectiveLine.normalizedVector e d) (i.2 r) ≠ 0 := by
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
      (directionMap_ne_zero c r _ (ProjectiveLine.normalizedVector_ne_zero e d))).mp hr

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
    restrictionFactor c a b e j d * FixedFiberBundle.gain c.t a b i j (param c d) =
      restrictionFactor c a b e i d := by
  obtain ⟨hbi,hri⟩ := restrictionPatch_coordinates c e i d hi
  obtain ⟨hbj,hrj⟩ := restrictionPatch_coordinates c e j d hj
  change _ * (ProjectivePlaneBundle.gain a i.1 j.1 (base c d) *
    ∏ r,ProjectiveLineBundle.gain (b r) (i.2 r) (j.2 r) (direction c r d)) = _
  simp only [ProjectivePlaneBundle.gain,ProjectiveLineBundle.gain]
  rw [base_normalizedVector c e d hi.1,ProjectivePlane.bundle_ratio_vectorPoint _ _ _ hbj]
  have hrat : ∀ r, ProjectiveLineBundle.ratio (i.2 r) (j.2 r) (direction c r d) =
      directionMap c r (ProjectiveLine.normalizedVector e d) (i.2 r) /
        directionMap c r (ProjectiveLine.normalizedVector e d) (j.2 r) := by
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
  simp only [map_smul,Pi.smul_apply,smul_eq_mul,mul_zpow]
  rw [Finset.prod_mul_distrib]
  have hp : (R^2)^a = R^(2*a) := by rw [zpow_mul]; norm_cast
  have hsum : (∏ r : Fin 4, R ^ b r) = R ^ (∑ r, b r) := by
    rw [Fin.prod_univ_four,Fin.sum_univ_four]
    simp only [zpow_add₀ hR]
  change (R^2)^a * _ * ((∏ r : Fin 4, R ^ b r) * _) = _
  rw [hp,hsum]
  change _ = R^(2*a + ∑ r,b r) * _
  rw [zpow_add₀ hR]
  ring

/-- Exact two-sided cocycle identity on the actual refined cover. -/
theorem restrictionFactor_change (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (e f : Fin 2) (i j : Frame) (d : Direction)
    (hi : d ∈ restrictionPatch c e i) (hj : d ∈ restrictionPatch c f j) :
    restrictionFactor c a b f j d * FixedFiberBundle.gain c.t a b i j (param c d) =
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
      (fun d => directionMap c r (ProjectiveLine.normalizedVector e d) (i.2 r))
      (restrictionPatch c e i) :=
    (contDiff_apply ℂ ℂ (i.2 r)).contMDiff.comp_contMDiffOn
      ((directionMap_contDiff c r n).contMDiff.comp_contMDiffOn hv)
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
end FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
