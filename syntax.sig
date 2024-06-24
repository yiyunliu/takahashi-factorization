tm : Type

tAbs : (tm -> tm) -> tm
tApp : tm -> tm -> tm
tIf : tm -> tm -> tm -> tm
tTrue : tm
tFalse : tm