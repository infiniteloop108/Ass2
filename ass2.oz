\include 'SingleAssignmentStore.oz'

declare
Env={Dictionary.new}

declare
TotVar={NewCell 0}

declare
fun {GetID}
   TotVar:=@TotVar+1
   @TotVar
end

declare
fun {EnvMap Env X}
   {Dictionary.get Env X}
end

declare
proc {Run S E}
   {Browse S}
   {Browse {Dictionary.entries E}}
   %If S is not a list, then there is a syntax error 
   case S
   of X|Y then skip
   else {Browse 'Compile Error'}
   end
   %Try and search for valid syntax, else consider it as a sequence of statements
   case S
   of [nop] then skip
   [] [localvar ident(X) S] then
      local NE in
	 NE={Dictionary.clone E}
	 {Dictionary.put NE X {GetID}}
	 {Run S NE}
      end
   [] [bind ident(x) ident(y)] then
      if {Dictionary.member E x}==false then {Browse 'Variable not declared'}
      elseif {Dictionary.member E y}==false then {Browse 'Variable not declared'}
      else {UnifySAS {EnvMap E y} {EnvMap E y}}
      end
   else
      %It is a sequence of statements
      {Run S.1 E}
      if S.2 \= nil then
	 {Run S.2 E}
      end
   end
end

{Run [localvar ident(x) [ [localvar ident(x) [  [localvar ident(x) [nop]] [nop] [nop] ] ] [nop]  [nop]] ] Env}
%{Dictionary.put Env haha 2}
%{Browse {Dictionary.get Env haha}}