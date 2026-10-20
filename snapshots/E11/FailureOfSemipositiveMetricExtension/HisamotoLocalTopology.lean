import FailureOfSemipositiveMetricExtension.HisamotoIncidence
import FailureOfSemipositiveMetricExtension.ProjectiveLineBundle

/-! The ruling product is a genuine homeomorphism for the inherited incidence
subspace topology. Polynomial representatives certify the ambient analytic maps;
no continuity of a chosen homogeneous representative is assumed. -/
namespace FailureOfSemipositiveMetricExtension.Hisamoto
noncomputable section
open Set Topology
open scoped Manifold ContDiff

instance instTopologicalSpacePoint : TopologicalSpace Point :=
  inferInstanceAs (TopologicalSpace {q : PlanePoint × Direction // Incidence q.1 q.2})

/-- The two homogeneous coordinates recovering `[x:s]` over a ruling chart. -/
def fiberProjection (i : Fin 2) : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := if i = 0 then ![v 0,v 1] else ![v 0,v 2]
  map_add' v w := by fin_cases i <;> ext j <;> fin_cases j <;> simp
  map_smul' c v := by fin_cases i <;> ext j <;> fin_cases j <;> simp

@[simp] theorem fiberProjection_fiberLinear (i : Fin 2) (t : ℂ) (v : Fin 2 → ℂ) :
    fiberProjection i (fiberLinear i t v) = v := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [fiberProjection,fiberLinear,directionVector,Blowup.vectorX,Blowup.vectorY]

def fiberDirection (i : Fin 2) (p : PlanePoint) : Direction :=
  ProjectiveLine.vectorPoint (fiberProjection i p.rep)

theorem vectorPoint_smul (a : ℂˣ) (v : Fin 2 → ℂ) :
    ProjectiveLine.vectorPoint (a • v) = ProjectiveLine.vectorPoint v := by
  by_cases hv : v = 0
  · simp [hv]
  · have hn : a • v ≠ 0 := by
      change (a : ℂ) • v ≠ 0
      exact smul_ne_zero (Units.ne_zero a) hv
    rw [ProjectiveLine.vectorPoint_eq_mk _ hn,ProjectiveLine.vectorPoint_eq_mk _ hv]
    exact (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr ⟨a,rfl⟩

theorem fiberDirection_mk (i : Fin 2) (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    fiberDirection i (Projectivization.mk ℂ v hv) = ProjectiveLine.vectorPoint (fiberProjection i v) := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  unfold fiberDirection
  rw [← ha]
  change ProjectiveLine.vectorPoint (fiberProjection i ((a : ℂ) • v)) = _
  rw [map_smul]
  exact vectorPoint_smul a _

@[simp] theorem fiberDirection_fiberPlane (i : Fin 2) (t : ℂ) (p : Direction) :
    fiberDirection i (fiberPlane i t p) = p := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [fiberPlane,Projectivization.map_mk,fiberDirection_mk,fiberProjection_fiberLinear,
      ProjectiveLine.vectorPoint_eq_mk _ hv]

/-- All homogeneous functions used below are polynomial in local coordinates. -/
theorem directionVector_contDiff (i : Fin 2) (n : WithTop ℕ∞) :
    ContDiff ℂ n (directionVector i) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [directionVector,Blowup.vectorX,Blowup.vectorY] <;> fun_prop

theorem fiberVector_contDiff (i j : Fin 2) (n : WithTop ℕ∞) :
    ContDiff ℂ n (fun q : ℂ × ℂ => fiberLinear i q.2 (directionVector j q.1)) := by
  apply contDiff_pi.mpr
  intro k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [fiberLinear,directionVector,Blowup.vectorX,Blowup.vectorY] <;> fun_prop

theorem fiberVector_nonzero (i j : Fin 2) (q : ℂ × ℂ) :
    fiberLinear i q.2 (directionVector j q.1) ≠ 0 :=
  (map_ne_zero_iff _ (fiberLinear_injective i q.2)).mpr (directionVector_ne_zero j q.1)

theorem fiberPlane_param_eq (i j : Fin 2) (q : ℂ × ℂ) :
    fiberPlane i q.2 (ProjectiveLine.param j q.1) =
      ProjectivePlane.vectorPoint (fiberLinear i q.2 (directionVector j q.1)) := by
  rw [← directionVector_mk j q.1,fiberPlane,Projectivization.map_mk,
    ProjectivePlane.vectorPoint_eq_mk _ (fiberVector_nonzero i j q)]

theorem fiberPlane_param_contMDiff (i j : Fin 2) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,ℂ × ℂ) 𝓘(ℂ,ℂ × ℂ) n
      (fun q : ℂ × ℂ => fiberPlane i q.2 (ProjectiveLine.param j q.1)) := by
  intro q
  simp_rw [fiberPlane_param_eq]
  exact (ProjectivePlane.vectorPoint_contMDiffAt n _ (fiberVector_nonzero i j q)).comp q
    (fiberVector_contDiff i j n).contMDiff.contMDiffAt

abbrev productModel := 𝓘(ℂ).prod 𝓘(ℂ)

theorem fiberPlane_contMDiff (i : Fin 2) (n : WithTop ℕ∞) :
    ContMDiff productModel 𝓘(ℂ,ℂ × ℂ) n (fun q : Direction × ℂ => fiberPlane i q.2 q.1) := by
  intro q
  obtain ⟨j,s,hs⟩ := ProjectiveLine.charts_cover q.1
  have hj : q.1 ∈ ProjectiveLine.chartSet j := ⟨s,hs.symm⟩
  have hc := ((ProjectiveLineBundle.coordinates_contMDiffOn j n).contMDiffAt
    ((ProjectiveLine.chartSet_isOpen j).mem_nhds hj)).comp q
      (show ContMDiffAt productModel 𝓘(ℂ) n Prod.fst q from contMDiffAt_fst)
  have hh := (fiberPlane_param_contMDiff i j n).contMDiffAt.comp q
    (hc.prodMk_space contMDiffAt_snd)
  apply hh.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.eventually
    ((ProjectiveLine.chartSet_isOpen j).mem_nhds hj)] with q' hq'
  exact congrArg (fiberPlane i q'.2) (ProjectiveLine.param_coordinates j q'.1 hq').symm

theorem fiberProjection_contDiff (i : Fin 2) (n : WithTop ℕ∞) :
    ContDiff ℂ n (fiberProjection i) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [fiberProjection] <;> fun_prop

theorem planeVector_contDiff (a : Fin 3) (n : WithTop ℕ∞) :
    ContDiff ℂ n (ProjectivePlane.vector a) := by
  apply contDiff_pi.mpr
  intro k
  fin_cases a <;> fin_cases k <;> dsimp [ProjectivePlane.vector] <;> fun_prop

theorem fiberProjection_rep_nonzero_of_fiberPlane (i : Fin 2) (t : ℂ) (p : Direction) :
    fiberProjection i (fiberPlane i t p).rep ≠ 0 := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [fiberPlane,Projectivization.map_mk]
    obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
      (fiberLinear i t v) (by exact (map_ne_zero_iff _ (fiberLinear_injective i t)).mpr hv)
    rw [← ha]
    change fiberProjection i ((a : ℂ) • fiberLinear i t v) ≠ 0
    rw [map_smul,fiberProjection_fiberLinear]
    exact smul_ne_zero (Units.ne_zero a) hv

theorem fiberProjection_rep_nonzero (i : Fin 2) (q : Point) (hq : q ∈ rulingChart i) :
    fiberProjection i (blowdown q).rep ≠ 0 := by
  rw [rulingChart_eq_range] at hq
  obtain ⟨⟨p,t⟩,rfl⟩ := hq
  exact fiberProjection_rep_nonzero_of_fiberPlane i t p

theorem fiberDirection_contMDiffAt (i : Fin 2) (n : WithTop ℕ∞) (p : PlanePoint)
    (hp : fiberProjection i p.rep ≠ 0) :
    ContMDiffAt 𝓘(ℂ,ℂ × ℂ) 𝓘(ℂ) n (fiberDirection i) p := by
  obtain ⟨a,v,hv⟩ := ProjectivePlane.charts_cover p
  have ha : p ∈ ProjectivePlane.chartSet a := ⟨v,hv.symm⟩
  have hn : fiberProjection i (ProjectivePlane.vector a (ProjectivePlane.coordinates a p)) ≠ 0 := by
    have he : ProjectivePlane.param a (ProjectivePlane.coordinates a p) = p :=
      ProjectivePlane.param_coordinates a p ha
    obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
      (ProjectivePlane.vector a (ProjectivePlane.coordinates a p))
      (ProjectivePlane.vector_nonzero a _)
    change c • ProjectivePlane.vector a (ProjectivePlane.coordinates a p) =
      (ProjectivePlane.param a (ProjectivePlane.coordinates a p)).rep at hc
    rw [he] at hc
    intro hz
    apply hp
    rw [← hc]
    change fiberProjection i ((c : ℂ) • _) = 0
    rw [map_smul,hz,smul_zero]
  have hc := (ProjectivePlaneBundle.coordinates_contMDiffOn a n).contMDiffAt
    ((ProjectivePlane.chartSet_isOpen a).mem_nhds ha)
  have hm := ((fiberProjection_contDiff i n).comp (planeVector_contDiff a n)).contMDiff.contMDiffAt.comp p hc
  apply ((ProjectiveLine.vectorPoint_contMDiffAt n _ hn).comp p hm).congr_of_eventuallyEq
  filter_upwards [(ProjectivePlane.chartSet_isOpen a).mem_nhds ha] with p' hp'
  have he := fiberDirection_mk i (ProjectivePlane.vector a (ProjectivePlane.coordinates a p'))
    (ProjectivePlane.vector_nonzero a _)
  change fiberDirection i (ProjectivePlane.param a (ProjectivePlane.coordinates a p')) = _ at he
  rwa [ProjectivePlane.param_coordinates a p' hp'] at he

theorem blowdown_continuous : Continuous blowdown := continuous_fst.comp continuous_subtype_val
theorem ruling_continuous : Continuous ruling := continuous_snd.comp continuous_subtype_val

theorem rulingChart_isOpen (i : Fin 2) : IsOpen (rulingChart i) :=
  (ProjectiveLine.chartSet_isOpen i).preimage ruling_continuous

theorem localParam_continuous (i : Fin 2) : Continuous (localParam i) :=
  ((fiberPlane_contMDiff i 0).continuous.prodMk
    ((ProjectiveLine.param_continuous i).comp continuous_snd)).subtype_mk _

def localCoordinates (i : Fin 2) (q : Point) : Direction × ℂ :=
  (fiberDirection i (blowdown q),ProjectiveLine.coordinates i (ruling q))

@[simp] theorem localCoordinates_localParam (i : Fin 2) (q : Direction × ℂ) :
    localCoordinates i (localParam i q) = q := by
  simp [localCoordinates]

theorem localParam_localCoordinates (i : Fin 2) (q : Point) (hq : q ∈ rulingChart i) :
    localParam i (localCoordinates i q) = q := by
  rw [rulingChart_eq_range] at hq
  obtain ⟨p,rfl⟩ := hq
  rw [localCoordinates_localParam]

theorem localCoordinates_continuousOn (i : Fin 2) : ContinuousOn (localCoordinates i) (rulingChart i) := by
  intro q hq
  have hf := ((fiberDirection_contMDiffAt i 0 (blowdown q)
    (fiberProjection_rep_nonzero i q hq)).continuousAt.comp blowdown_continuous.continuousAt)
  have hb := ((ProjectiveLine.homeomorphChart i).continuousOn.continuousAt
    ((ProjectiveLine.chartSet_isOpen i).mem_nhds hq)).comp ruling_continuous.continuousAt
  exact (hf.prodMk hb).continuousWithinAt

/-- Actual open product chart, with source the ruling preimage and all `P¹×ℂ` as target. -/
def rulingProductChart (i : Fin 2) : PartialHomeomorph Point (Direction × ℂ) where
  toFun := localCoordinates i
  invFun := localParam i
  source := rulingChart i
  target := univ
  map_source' _ _ := mem_univ _
  map_target' q _ := by rw [rulingChart_eq_range]; exact ⟨q,rfl⟩
  left_inv' := localParam_localCoordinates i
  right_inv' q _ := localCoordinates_localParam i q
  open_source := rulingChart_isOpen i
  open_target := isOpen_univ
  continuousOn_toFun := localCoordinates_continuousOn i
  continuousOn_invFun := (localParam_continuous i).continuousOn

/-- The inherited topology on the actual incidence surface has genuine open products. -/
def localProductHomeomorph (i : Fin 2) : (Direction × ℂ) ≃ₜ rulingChart i where
  toEquiv := localProduct i
  continuous_toFun := (localParam_continuous i).subtype_mk _
  continuous_invFun := by
    have h : Continuous (fun q : rulingChart i => localCoordinates i q.val) :=
      (localCoordinates_continuousOn i).restrict
    convert h using 1
    funext q
    apply (localProduct i).injective
    apply Subtype.ext
    exact (congrArg Subtype.val ((localProduct i).apply_symm_apply q)).trans
      (localParam_localCoordinates i q.val q.property).symm

end
end FailureOfSemipositiveMetricExtension.Hisamoto
