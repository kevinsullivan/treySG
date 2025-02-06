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
(vehicles : Set Vehicle := { egoVehicle} ∪ otherVehicles)
(stopSigns : Set StopSign)

-- relations
(ssControlsLane : StopSign → Lane → Bool)
(vehInLane : Vehicle → Lane → Bool)

-- entities
(lanesControledBySS : Set Lane := { l ∈ lanes |  ∀ ss ∈ stopSigns, ssControlsLane ss l })
(vehicleLanes : Vehicle → Set Lane := λ v => { l ∈ lanes | ∀ veh ∈ vehicles, vehInLane veh l})
(egoLanes : Set Lane := vehicleLanes egoVehicle)

-- properties
(vehHasStop (v : Vehicle) : Prop := ∃ l, l ∈ vehicleLanes v ∩ lanesControledBySS)
(egoHasStop : Prop := vehHasStop egoVehicle)

end TreySG.SG
