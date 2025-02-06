import Mathlib.Data.Set.Basic

namespace TreySG.SG

structure Lane : Type where
(id : Nat)
deriving Repr

structure Vehicle : Type where
(id : Nat)
deriving Repr

structure StopSign : Type where
(id : Nat)

structure SceneGraph : Type 1 where

-- entities
(lanes : Set Lane)
(egoVehicle : Vehicle)
(otherVehicles : Set Vechicle)
(egoInvariant : egoVehicle ∉ otherVehicles)
(vechicles : Set Vehicle := { egoVehicle} ∪ otherVehicles)
(stopSigns : Set StopSign)

-- relations
(ssControlsLane : StopSign → Lane → Bool)
(vehInLane : Vehicle → Lane → Bool)
(hasStop : Prop :=
  let egoLanes := { l ∈ lanes | vehInLane egoVehicle l}
  let lanesWithSS := { l ∈ lanes |  ∀ ss ∈ stopSigns, ssControlsLane ss l }
  egoLanes ∩ lanesWithSS ≠ {})

end TreySG.SG
