\begin{code}
{-# OPTIONS --sized-types #-}

open import Size
open import Data.Fin
  using (
    Fin
  )
open import Function
  using (
    _∘_;
    _$_
  )
open import Data.List
  using (
    List
  )
open import Data.List
  using (
    List
  )
open import Data.Product
  using (
    _×_;
    Σ
  )
open import Codata.Colist
  using (
    Colist
  )

import Data.Integer
  as ℤ

ℝ : Set
ℝ = ℤ.ℤ × Colist (Fin 10) ∞

0ℝ : ℝ
0ℝ = {!!}

1ℝ : ℝ
1ℝ = {!!}

_≥_ : ℝ → ℝ → Set
_≥_ = {!!}

_<_ : ℝ → ℝ → Set
_<_ = {!!}

Intensity : Set
Intensity = Σ ℝ $ λ q → 1ℝ ≥ q × q ≥ 0ℝ

ElectroMagneticWavelength : Set
ElectroMagneticWavelength = Σ ℝ $ _<_ 0ℝ

Colour : Set
Colour = List $ ElectroMagneticWavelength × Intensity
\end{code}
