\documentclass{article}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{∋}{\ensuremath{\mathnormal\ni}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{∶}{\ensuremath{\mathnormal\colon\!\!}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb F}}}
\newunicodechar{𝕄}{\ensuremath{\mathnormal{\mathbb M}}}
\newunicodechar{𝕊}{\ensuremath{\mathnormal{\mathbb S}}}
\newunicodechar{𝔹}{\ensuremath{\mathnormal{\mathbb B}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal{\mathbb Z}}}
\newunicodechar{ℝ}{\ensuremath{\mathnormal{\mathbb R}}}
\newunicodechar{ν}{\ensuremath{\mathnormal\nu}}
\newunicodechar{μ}{\ensuremath{\mathnormal\mu}}
\newunicodechar{τ}{\ensuremath{\mathnormal\tau}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{ˡ}{\ensuremath{\mathnormal{^\AgdaFontStyle{l}}}}
\newunicodechar{ʳ}{\ensuremath{\mathnormal{^\AgdaFontStyle{r}}}}
\newunicodechar{≥}{\ensuremath{\mathnormal\geq}}
\newunicodechar{≮}{\ensuremath{\mathnormal\nless}}
\newunicodechar{ϕ}{\ensuremath{\mathnormal\phi}}
\newunicodechar{∧}{\ensuremath{\mathnormal\wedge}}
\newunicodechar{∣}{\ensuremath{\mathnormal |}}
\newunicodechar{∘}{\ensuremath{\mathnormal\circ}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal\ell}}
\newunicodechar{σ}{\ensuremath{\mathnormal\sigma}}
\newunicodechar{π}{\ensuremath{\mathnormal\pi}}
\newunicodechar{α}{\ensuremath{\mathnormal\alpha}}
\newunicodechar{₀}{\ensuremath{\mathnormal{_0}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_\AgdaFontStyle{i}}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_\AgdaFontStyle{l}}}}
\newunicodechar{ₓ}{\ensuremath{\mathnormal{_\AgdaFontStyle{x}}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_\AgdaFontStyle{v}}}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_\AgdaFontStyle{m}}}}
\newunicodechar{ₚ}{\ensuremath{\mathnormal{_\AgdaFontStyle{p}}}}
\newunicodechar{≤}{\ensuremath{\mathnormal\leq}}
\newunicodechar{⍉}{\ensuremath{\mathnormal{∘\hspace{-0.455em}\backslash}}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}
\newunicodechar{δ}{\ensuremath{\mathnormal\delta}}
\newunicodechar{⇒}{\ensuremath{\mathnormal\Rightarrow}}
\newunicodechar{↔}{\ensuremath{\mathnormal\leftrightarrow}}
\newunicodechar{≰}{\ensuremath{\mathnormal\nleq}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\hspace{-0.3em}|}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{|\hspace{-0.3em}\rbrace}}}
\newunicodechar{▹}{\ensuremath{\mathnormal\triangleright}}
\newunicodechar{⊓}{\ensuremath{\mathnormal\sqcap}}
\newunicodechar{⍨}{\raisebox{-0.25ex}{$\ddot\sim$}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\title{le velcki be le se ctaipe be le ro se skari / The Definition of the Type of All Colours}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le krinu}
\paragraph{la .lojban.}
ni'o le pilno be la'oi .Discord. cu cpedu lo nu su'o da poi ke'a skari zo'u la .varik. cu skicu da fo lo .indika be tu'a lo no se skari poi ke'a na du da  .i la'e di'u krinu le nu la .varik. cu ciksi le ctaipe be lo ro se skari

\paragraph{English}
A user of Discord requests that VARIK writes a description (of a colour $s$) $v$ such that $v$ references no colour which is not $s$.  That (the user requests) justifies that VARIK defines the type of all colours.

\section{le vrici / The Miscellaneous}

\begin{code}
{-# OPTIONS --sized-types #-}

open import Size
  using (
    ∞
  )
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
    _,_;
    Σ
  )
open import Codata.Colist
  using (
    Colist
  )

import Data.Integer
  as ℤ
\end{code}

\section{la'oi .\F ℝ.}
\paragraph{la .lojban.}
ni'o la'oi .\F ℝ.\ ctaipe lo ro mrena'u  .i ro da poi ke'a ctaipe la'oi .\F ℝ.\ zo'u da du lo namcu poi ke'a sumji ko'a goi lo mu'oi zoi.\ \AgdaField{proj₁}\ .zoi.\ be da bei lo pilji be lo se ke me'oi .decimal. sinxa be lo mu'oi zoi.\ \AgdaField{proj₂}\ .zoi.\ be ke'a be'o be'o bei zo'e poi ga jonai ga je ko'a dubjavmau li no gi da du li pa gi da du li ni'u pa
\end{itemize}

\paragraph{English}
\F ℝ is the type of all real numbers.  For all real numbers $r$, $r \geq 0$ iff $r$ equals the \F ℝ \B s such that (\AgdaField{proj₁} \B s\ is the floor of $r$, and \AgdaField{proj₂} \B s\ represents a thing $t$ such that $r$ equals the sum of $t$ and the floor of $r$.  For all real numbers $r$, $r \ngeq 0$ iff $r$ equals the \F ℝ \B s such that (\AgdaField{proj₁} \B s\ is the floor of $r$, and \AgdaField{proj₂} \B s\ represents a thing $t$ such that $r$ equals the sum of $t$ and the negation of the floor of $r$.

\begin{code}
ℝ : Set
ℝ = ℤ.ℤ × Colist (Fin 10) ∞
\end{code}

\subsection{le ctaipe be la'oi .\F ℝ.\ be'o poi pilno ke'a tu'a lo se skari / The Values (of ℝ) which are Used for the Colours}

\subsubsection{la'oi .\F{0ℝ}.}
\paragraph{la .lojban.}
ni'o la'oi .\F{0ℝ}.\ du li no

\paragraph{English}
\F{0ℝ} is 0.

\begin{code}
0ℝ : ℝ
0ℝ = ℤ.0ℤ , Colist.[]
\end{code}

\subsubsection{la'oi .\F{1ℝ}.}
\paragraph{la .lojban.}
ni'o la'oi .\F{1ℝ}.\ du li pa

\paragraph{English}
\F{1ℝ} is 1.

\begin{code}
1ℝ : ℝ
1ℝ = ℤ.1ℤ , Colist.[]
\end{code}

\subsection{le fancu pe la'oi .\F ℝ. / Functions of ℝ}

\subsubsection{la'oi .\F{\AgdaUnderscore{}≥\AgdaUnderscore}.}
\paragraph{la .lojban.}
ni'o ga jo ctaipe la'o zoi.\ \B x \OpF ≥ \B z\ .zoi.\ gi la'oi .\B x.\ dubjavmau la'oi .\B z.

\paragraph{English}
A proof of \B x \OpF ≥ \B z\ exists iff \B x exceeds (or equals) \B z.

\begin{code}
_≥_ : ℝ → ℝ → Set
_≥_ = {!!}
\end{code}

\subsubsection{la'oi .\F{\AgdaUnderscore{}<\AgdaUnderscore}.}
\paragraph{la .lojban.}
ni'o ga jo ctaipe la'o zoi.\ \B x \OpF < \B z\ .zoi.\ gi la'oi .\B x.\ mleca la'oi .\B z.

\paragraph{English}
A proof of \B x \OpF < \B z\ exists iff \B z exceeds \B x.

\begin{code}
_<_ : ℝ → ℝ → Set
_<_ = {!!}
\end{code}

\section{la'oi .\F{Intensity}.}

\begin{code}
Intensity : Set
Intensity = Σ ℝ $ λ q → 1ℝ ≥ q × q ≥ 0ℝ
\end{code}

\section{la'oi .\F{ElectroMagneticWavelength}.}

\begin{code}
ElectroMagneticWavelength : Set
ElectroMagneticWavelength = Σ ℝ $ _<_ 0ℝ
\end{code}

\section{la'oi .\F{Colour}.}

\begin{code}
Colour : Set
Colour = List $ ElectroMagneticWavelength × Intensity
\end{code}
\end{document}
