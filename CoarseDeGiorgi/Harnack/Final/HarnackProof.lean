import CoarseDeGiorgi.Statements.WeakHarnack
import CoarseDeGiorgi.Harnack.Final.Harnack

namespace CoarseDeGiorgi

theorem harnack_proved :
    type_of% (Harnack.Final.harnack_proved CoarseDeGiorgi.weak_harnack) :=
  Harnack.Final.harnack_proved CoarseDeGiorgi.weak_harnack

end CoarseDeGiorgi
