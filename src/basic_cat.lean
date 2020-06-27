
import category_theory.functor_category
--import field_theory.splitting_field
--import field_theory.subfield
import algebra.field
import algebra.ring
--import ring_theory.algebra
--import ring_theory.algebraic
import category_theory.isomorphism
import algebra.group.hom
import data.set.basic

open category_theory
universes v u
--variables (k : Type u) [𝕜 :field k] (L : Type u) [𝕃 :field L] (F : Type u) [𝔽 :field F]
structure fields : Type (u+1) :=
(k : Type u)
(fStruct : field k)


instance fields_to_sort : has_coe_to_sort fields :=
{S := Type u, coe := λ F, F.k} 
instance fieldIsField (a : fields) : field a := a.fStruct

instance fields_has_hom : has_hom fields :=
{ hom:= λ a b, ring_hom a b }
instance fields_has_cat_struct : category_struct fields :=
{to_has_hom:= fields_has_hom, id:=λ X, ring_hom.id X, comp := λ a b c fab fbc,ring_hom.comp fbc fab }


structure fieldsOver (L : fields.{u}) : Type (u+1)  :=
(k : fields.{u})
(L2k : L →+* k )

instance ext_fields_coe (L : fields.{u}) : has_coe (fieldsOver L) fields.{u}:=
⟨fieldsOver.k⟩

@[ext] structure kLinearMor {L : fields.{u}} (k₁ k₂ : fieldsOver L) : Type u :=
(mor : k₁ →+* k₂ )
(coincide : ring_hom.comp mor k₁.L2k = k₂.L2k )


instance morphism_to_fun {L : fields.{u}} (k₁ k₂ : fieldsOver L) :
  has_coe_to_fun ( kLinearMor k₁ k₂) :=
{ F   := λ _, k₁ → k₂,
  coe := λ m, m.mor }

instance ext_fields_has_hom (L : fields.{u}) : has_hom (fieldsOver L) :=
{hom := kLinearMor }

instance ext_fields_has_cat_struct (L : fields.{u}) : category_struct (fieldsOver L) :=
{to_has_hom:= ext_fields_has_hom L, id:=λ X, {mor :=  ring_hom.id X, coincide:= ring_hom.id_comp _ },
 comp := λ a b c fab fbc,⟨ring_hom.comp fbc.mor fab.mor, by rw [ring_hom.comp_assoc,fab.coincide,fbc.coincide] ⟩ }

/- variables (L : fields.{u})(X Y Z :fieldsOver L)
#check (ext_fields_has_cat_struct L).comp
#check kLinearMor.mor (𝟙X)
 -/
instance ext_fields_cat (L : fields.{u}): category (fieldsOver L):=
{
  to_category_struct := ext_fields_has_cat_struct L,

  id_comp' :=begin  intros X Y fXY ,ext,
  dsimp [kLinearMor.mor],
   refl, end  , 
   
  comp_id':=begin  intros X Y fXY ,ext,
  dsimp [kLinearMor.mor],
   refl, end  ,
  
  assoc' := begin intros W X Y Z f g h ,ext,
  dsimp [kLinearMor.mor],
   refl, end  
  }


/- structure subFields (F : Type u) [𝔽 :field F] : Type (u+1):=
(k : Type u)
(𝕜 :field k)
(k2F : k →+* F ) -/






 def AutGrp (L : fields.{u})(F : fieldsOver L):Type u :=
 --F ≃ₐ[L] F
 F ≅ F


--notation `Aut(`:30 F `/` L  := AutGrp L F




instance aut_grp_struct (L : fields.{u})(F : fieldsOver L) : group (AutGrp L F) :=
{ mul:= λ a b, iso.trans b a,
  mul_assoc := begin intros a b c, ext, simp, end,
  one := iso.refl F,
  one_mul := begin intro a, ext,simp,refl,  end,
  mul_one := begin intro a, ext,simp, refl, end,
  inv := iso.symm,
  mul_left_inv := category_theory.iso.self_symm_id
} 
/- { mul:= alg_equiv.trans,
  mul_assoc := begin intros a b c, ext, simp, refl, end,
  one := alg_equiv.refl,
  one_mul := begin intro a, ext,simp, refl, end,
  mul_one := begin intro a, ext,simp, refl, end,
  inv := alg_equiv.symm,
  mul_left_inv := begin intro a,ext,simp,rw a.left_inv, end

} -/

structure fieldsBetween (L : fields.{u})(F : fieldsOver L)   :Type (u+1)  :=
(k:fieldsOver L)
(k2F : k ⟶ F)
instance bet_fields_coe (L : fields.{u})(F : fieldsOver L) : has_coe (fieldsBetween L F) (fieldsOver L) :=
⟨fieldsBetween.k⟩

variables (L : fields.{u})(F : fieldsOver L)(E : fieldsOver F.k)


instance inbeding_coe : has_coe (fieldsOver F.k) (fieldsOver L ):=
⟨ λ E, {k:= E.k, L2k:= ring_hom.comp E.L2k F.L2k }⟩

lemma induce1 : (↑E: fieldsOver L).L2k = ring_hom.comp E.L2k F.L2k :=
begin ext,refl, end

def base_change_functor : functor (fieldsOver F.k) (fieldsOver L) :=
{
  obj := λ E , ↑E,
  map := λ A B f , ⟨f.mor, begin cases f,dsimp,rw [induce1,induce1, ←ring_hom.comp_assoc ,f_coincide], end ⟩,
  map_id':= begin intro X, ext, refl, end,
  map_comp':= begin intros X Y Z f g, ext,refl, end
}


instance AutSubGrp_lift : has_lift (AutGrp F.k E) (AutGrp L ↑E) :=
⟨functor.map_iso (base_change_functor L F)⟩

lemma lift_inj(g: AutGrp F.k E) : ⇑(g.hom.mor)=(↑ g : (AutGrp L ↑E)).hom.mor :=
begin ext, refl, end

def AutSubGrp : monoid_hom (AutGrp F.k E) (AutGrp L ↑E) :=
{ to_fun :=λ g, ↑g,
  map_one' := by refl,
  map_mul' := begin intros x y, ext, refl, end,
}

lemma AutSub_inj : function.injective ⇑(AutSubGrp L F E) :=
begin 
rw monoid_hom.injective_iff,
intros a h,
apply iso.ext,
have h0 : ⇑(AutSubGrp L F E)  = λa, ↑a := by refl,
rw h0 at h, dsimp at h,
have h1:= (lift_inj _ _ _ a),
rw h at h1, symmetry,
ext, rw h1,refl,
end



def normal_ext(F: fieldsOver L) :  Prop :=
∀ (K : fieldsOver L) (f g : F ⟶ K) , set.range f = set.range g