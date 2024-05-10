\begin{code}
import Data.Integer
  as ℤ
open import Data.List
  using (
    List
  )
open import Data.Product
  using (
    _×_;
    Σ
  )
open import Data.Rational
  as ℚ
  using (
    ℚ
  )

Intensity : Set
Intensity = Σ ℚ $ λ q → ℚ.1ℚ ℚ.≥ q × q ℚ.≥ ℚ.0ℚ

ElectroMagneticWavelength : Set
ElectroMagneticWavelength = Σ ℚ $ ℤ._<_ ℤ.0ℤ ∘ ℚ.numerator

Colour : Set
Colour = List $ ElectroMagneticWavelength × Intensity
\end{code}
