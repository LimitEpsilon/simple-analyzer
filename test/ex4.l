port := 196;
len := 43;
pos := 139;
index := 14;
fd := 15;
xp := 1100;
count := 0;
i := &xp;
*i := xp + index + fd;
while (port < pos * 10) do (
    len := len + port;
    pos := pos * *i;
    index := index * port;
    xp := *i + 1010;
    fd := fd * port;
    *i := *i + 230000;
    if ((port + 1) < pos) 
    then index := index + xp
    else index := index + (-1)
)
