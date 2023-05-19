let fib n=
  let rec aux n a b=
    if n=0 then a else aux (n-1) b (a^b) in
  aux n "1" "0";;

let arg=Sys.argv;;

let test=fib (int_of_string(arg.(1)));;

let n=String.length(test);;

output_string stdout (string_of_int(1)^"\n");;
output_string stdout (string_of_int(n)^"\n");;
output_string stdout (string_of_int(0)^"\n");;
for i=0 to (n-1) do
 output_string stdout (string_of_int(i mod n)^"\t"^string_of_int((i+1) mod n)^"\t"^string_of_int(0)^"\n");
if test.[i]='1' then output_string stdout (string_of_int(i)^"\n")
done;;


