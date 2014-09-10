declare
fun {RE X}
   raise fucked(X) end
   2
end

declare
proc {My A}
   local X in
      X={RE A}
   end
end


try
   {My 2}
catch
   fucked(X) then {Browse 'Sorry!!'} {Browse X}
finally
   {Browse 'Thank You!'}
end


