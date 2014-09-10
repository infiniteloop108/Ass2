

%=============================================================================================
%For generating environment variables

declare
TotVar={NewCell 0}

declare
fun {GetID}
   %Function to generate a unique Environment variable for an identifier.
   TotVar:=@TotVar+1
   @TotVar
end

%=============================================================================================
%Function to return the environment variable for the identifier.

declare
fun {EnvMap Env X}
   %If it is not yet defined, then raise an exception
   if {Dictionary.member Env X}==false then raise varndec(X) end end
   %Return the mapped environment variable
   {Dictionary.get Env X}
end

%=============================================================================================
%Closure for procedures
%How do you match a pattern to a procedure?

declare
fun {Closure Env P}
   P
end

%=============================================================================================
%Function to map the identifiers in a value to the environment variables.

declare
fun {ValMap Env V}
   case V
   of H|T then {ValMap Env H}|{ValMap Env T}
   [] ident(X) then ident({EnvMap Env X})
   else V
   end
end

%=============================================================================================
%Main Interpreter

declare
proc {Interpret S}
   local Env Run in
      proc {Run S E}
	 %{Browse S}
	 %{Browse {Dictionary.entries E}}
         %If S is not a list, then there is a syntax error 
	 case S
	 of X|Y then skip
	 else raise stmerr(S) end
	 end
         %Try and search for valid syntax, else consider it as a sequence of statements
	 case S
	 of [nop] then skip
	 [] [localvar ident(X) S] then
	    local NE in
	       NE={Dictionary.clone E}
	       {Dictionary.put NE X {GetID}}
	       {SASAdd {Dictionary.get NE X}}
	       {Run S NE}
	    end
	 [] [bind ident(X) ident(Y)] then
            %Unify the two in the SAS
	    {UnifySAS {EnvMap E X} {EnvMap E Y}}
	 [] [bind ident(X) V] then
	    %Bind the value to X
	    {BindVal {EnvMap E X} {ValMap E V}}    
	 [] [conditional ident(X) S1 S2] then
	    local XSAS in
	       XSAS = {GetValFromSAS {EnvMap E X}}
       	       %To clarify
	       if XSAS==unBOUND then raise unbnd(X) end
	       else
		  if XSAS then {Run S1 E}
		  else {Run S2 E} end
	       end
	    end
	 else
            %It is a sequence of statements
	    {Run S.1 E}
	    if S.2 \= nil then
	       {Run S.2 E}
	    end
	 end
      end
      Env={Dictionary.new}
      {Run S Env}
   end
end

%=============================================================================================
%Try Programs

try
   {Interpret [localvar ident(x) [ [nop] [conditional ident(x) [nop] [nop]] ]]}
   %{Interpret [localvar ident(x) [ [localvar ident(x) [  [localvar ident(x) [nop]] [nop] [nop] ] ] [nop]  [nop]] ]}
   %{Interpret [localvar ident(x) [ [localvar ident(y) [  [localvar ident(x) [bind ident(x) [record literal(a) [ [literal(f1) ident(x)] [literal(f2) ident(y)] ]] ]] [nop] [nop] [bind ident(x) [record literal(a) [ [literal(f1) ident(x)] [literal(f2) ident(y)] ]] ] ] ] [nop]  [nop]  ] ]}
   %{Interpret [localvar ident(x) [localvar ident(y) [bind ident(x) ident(y)]]]}
   %{Interpret [localvar ident(x) [localvar ident(y) [localvar ident(x) [localvar ident(y) [bind ident(x) ident(y)]]]]]}
catch Err then
   case Err
   of stmerr(X) then {Browse X} {Browse 'Above is not a statement. Error!!'}
   [] varndec(X) then {Browse X} {Browse 'Above identifier has not been declared. Error!!'}
   [] unbnd(X) then {Browse X} {Browse 'Above variable was unbound at time of usage.'} %We do not have paraller programming for now, hence an error.
   [] illass(X Y) then {Browse X} {Browse Y} {Browse 'Illegal Assignment to an already bound variable'} %X is the environment variable
   else {Browse 'Unidentified Exception!!'}
   end
finally
   {Browse 'Thank you for using our interpreter' }
end

%=============================================================================================
