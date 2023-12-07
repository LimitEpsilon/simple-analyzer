w := read;
x := 2;
y := 4;
z := 3;
v := &x;
while (x > (-1)) do (
    x := *v + (- 1);
    y := y + 1;
    (if (z < 5)
      then goto 24
      else goto 29
    )
);
(if ((- 1) < *v)
  then goto 11
  else x := (- 1));
z := z + 1;
w := *v * w;
goto 20;
z := 0

(* [v |-> x ; w |-> 0 ; x |-> -1 ; y |-> 7 ; z |-> 0] *)
