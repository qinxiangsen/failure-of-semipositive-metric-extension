import FailureOfSemipositiveMetricExtension.GeneralTensorBundleIsomorphism
import FailureOfSemipositiveMetricExtension.GeneralAdjointObstruction

/-! The all-m theorem on actual tensor-product-valued canonical forms. Both
conversion maps use the proved analytic bundle isomorphism, and dt restriction
is an equality in the actual iterated tensor-product fibre. -/
namespace FailureOfSemipositiveMetricExtension.GeneralCao
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff TensorProduct

variable {n : ℕ} {M N : Type}
    [TopologicalSpace M] [ChartedSpace (Coord (n+1)) M]
    [TopologicalSpace N] [ChartedSpace (Coord n) N]
    {A B J : Type} (G : Family n M N A B) (L : AnalyticLine n (M := M) J) (m : ℕ)

structure TensorTotalAdjointSection where
  form : ∀ p : M, (TangentSpace 𝓘(ℂ,Coord (n+1)) p) [⋀^Fin (n+1)]→ₗ[ℂ] L.TensorFiber m p
  coefficient : B → J → M → ℂ
  analytic : ∀ b i, ContMDiffOn 𝓘(ℂ,Coord (n+1)) 𝓘(ℂ) ω
    (coefficient b i) (totalPatch n G (L.powerLine m) b i)
  represents : ∀ b i p, p ∈ totalPatch n G (L.powerLine m) b i →
    ∀ v : Fin (n+1) → TangentSpace 𝓘(ℂ,Coord (n+1)) p,
      (L.tensorTriv m i ⟨p,form p v⟩).2 = coefficient b i p *
        coordinateVolume (n+1)
          (fun k => mfderiv 𝓘(ℂ,Coord (n+1)) 𝓘(ℂ,Coord (n+1)) (G.totalAtlas.chart b) p (v k))

structure TensorCentralAdjointSection where
  form : ∀ p : N, (TangentSpace 𝓘(ℂ,Coord n) p) [⋀^Fin n]→ₗ[ℂ] L.TensorFiber m (G.inclusion p)
  coefficient : A → J → N → ℂ
  analytic : ∀ a i, ContMDiffOn 𝓘(ℂ,Coord n) 𝓘(ℂ) ω
    (coefficient a i) (centralPatch n G (L.powerLine m) a i)
  represents : ∀ a i p, p ∈ centralPatch n G (L.powerLine m) a i →
    ∀ v : Fin n → TangentSpace 𝓘(ℂ,Coord n) p,
      (L.tensorTriv m i ⟨G.inclusion p,form p v⟩).2 = coefficient a i p *
        coordinateVolume n
          (fun k => mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) (G.centralAtlas.chart a) p (v k))

def TensorCentralAdjointSection.toPower (s : TensorCentralAdjointSection G L m) :
    CentralAdjointSection n G (L.powerLine m) where
  form p := (L.tensorFiberEquiv m (G.inclusion p)).toLinearMap.compAlternatingMap (s.form p)
  coefficient := s.coefficient
  analytic := s.analytic
  represents a i p hp v := by
    change ((L.powerCore m).localTriv i (L.tensorBundleEquiv m ⟨G.inclusion p,s.form p v⟩)).2 = _
    rw [L.tensorBundleEquiv_localTriv m i ⟨G.inclusion p,s.form p v⟩ hp.2]
    exact s.represents a i p hp v

def TotalAdjointSection.toTensor (S : TotalAdjointSection n G (L.powerLine m)) :
    TensorTotalAdjointSection G L m where
  form p := (L.tensorFiberEquiv m p).symm.toLinearMap.compAlternatingMap (S.form p)
  coefficient := S.coefficient
  analytic := S.analytic
  represents b i p hp v := by
    change (L.tensorTriv m i ((L.tensorBundleEquiv m).symm ⟨p,S.form p v⟩)).2 = _
    rw [L.tensorBundleEquiv_symm_localTriv m i ⟨p,S.form p v⟩ hp.2]
    exact S.represents b i p hp v

def TensorRestrictsByDt (S : TensorTotalAdjointSection G L m) (s : TensorCentralAdjointSection G L m) : Prop :=
  ∀ (p : N) (ν : TangentSpace 𝓘(ℂ,Coord (n+1)) (G.inclusion p)),
    mfderiv 𝓘(ℂ,Coord (n+1)) 𝓘(ℂ) (fun x => (G.projection x : ℂ)) (G.inclusion p) ν = (1 : ℂ) →
      ∀ v : Fin n → TangentSpace 𝓘(ℂ,Coord n) p,
        S.form (G.inclusion p) (Fin.snoc
          (fun k => mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord (n+1)) G.inclusion p (v k)) ν) = s.form p v

theorem tensor_restriction_of_power (S : TotalAdjointSection n G (L.powerLine m))
    (s : TensorCentralAdjointSection G L m)
    (h : RestrictsByDt n G (L.powerLine m) S (s.toPower G L m)) :
    TensorRestrictsByDt G L m (S.toTensor G L m) s := by
  intro p ν hν v
  apply (L.tensorFiberEquiv m (G.inclusion p)).injective
  simpa only [TotalAdjointSection.toTensor,TensorCentralAdjointSection.toPower,
    LinearMap.compAlternatingMap_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] using h p ν hν v

def TensorPrescribedMultiplier (w₀ : J → N → WithBot ℝ) (s : TensorCentralAdjointSection G L m) : Prop :=
  PrescribedCentralPowerMultiplier G L w₀ m (s.toPower G L m)

variable [T2Space M] [SecondCountableTopology M] [IsManifold 𝓘(ℂ,Coord (n+1)) ω M]
    [T2Space N] [SecondCountableTopology N] [IsManifold 𝓘(ℂ,Coord n) ω N]

/-- Every positive tensor power, with both input and output actual alternating
forms valued in the genuine iterated tensor-product fibres. -/
theorem prescribed_metric_tensor_adjoint_extension_all_m
    (η : GeneralKahler.KahlerForm G.totalAtlas)
    (w₀ : J → N → WithBot ℝ)
    (hw₀ : ∀ p : N, ∃ q ∈ connectedComponent p, ∃ i : J,
      G.inclusion q ∈ L.core.baseSet i ∧ w₀ i q ≠ ⊥)
    (h : SemipositiveWeight n G L)
    (hrestrict : ∀ i p, G.inclusion p ∈ L.core.baseSet i → h.weight i (G.inclusion p) = w₀ i p)
    (hm : 0 < m) (s : TensorCentralAdjointSection G L m)
    (hs : TensorPrescribedMultiplier G L m w₀ s) :
    ∃ S : TensorTotalAdjointSection G L m, TensorRestrictsByDt G L m S s := by
  obtain ⟨S,hS⟩ := prescribed_metric_adjoint_extension_all_m G L η w₀ hw₀ h hrestrict m hm
    (s.toPower G L m) hs
  exact ⟨S.toTensor G L m,tensor_restriction_of_power G L m S s hS⟩

end
end FailureOfSemipositiveMetricExtension.GeneralCao
