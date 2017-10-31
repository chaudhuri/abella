sig stlc.

kind ty  type.
type b   ty.
type arr ty -> ty -> ty.

kind tm  type.
type abs ty -> (tm -> tm) -> tm.
type app tm -> tm -> tm.

type of  tm -> ty -> o.
type cp  tm -> tm -> o.