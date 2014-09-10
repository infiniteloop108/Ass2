%==============================
% declaring dictionary for SAS
declare
SAS = {Dictionary.new}

%===============================
% Add a new value in SAS
declare
proc {BindAdd X}
   {Dictionary.put SAS X [X unBOUND]}
end

%===============================
% Function for getting parent node in equivalence class

declare
fun {RetrieveNodeSAS Exp1}
   local Node in
      Node={Dictionary.get SAS Exp1}
      if Node.1==Exp1 then Node
      else {RetrieveNodeSAS Node.1}
      end
   end
end

%==============================
% function for getting value of a variable

declare
fun {RetrievefromSAS Exp1}
   local Node in
      Node={RetrieveNodeSAS Exp1}
      Node.2.1
   end
end

%================================
% Unifying two variables

declare
proc {UnifySAS Exp1 Exp2}

   {Browse {Dictionary.entries SAS}}
   local NodeX NodeY in
      NodeX = {RetrieveNodeSAS Exp1}
      NodeY = {RetrieveNodeSAS Exp2}
      case NodeX.2.1
      of unBOUND then
	 {Dictionary.put SAS NodeX.1 [NodeY.1 unBOUND]}
      else case NodeY.2.1
	   of unBOUND then {Dictionary.put SAS NodeY.1 [NodeX.1 unBOUND]}
	   else case NodeX.2.1 == NodeY.2.1
		of true then
		   {Dictionary.put SAS NodeX.1 [NodeY.1 unBOUND]}
		   {Dictionary.put SAS NodeY.1 [NodeY.1 NodeY.2.1]}
		[] false then
		   {Browse "Illegal assignment"}
		end
	   end
      end
   end
end

%===============================
% Binding a variable

declare
proc {Bindval Exp Val}
   local NodeX in
      NodeX={RetrieveNodeSAS Exp}
      {Browse NodeX.2.1}
      case NodeX.2.1
      of unBOUND then {Dictionary.put SAS NodeX.1 [NodeX.1 Val]} {Browse hi}
      else case NodeX.2.1==Val
	   of true then skip
	   [] false then {Browse 'Illegal assignment'}
	   end
      end
   end
end

%===========================
% Reset SAS
%
%{Dictionary.reset SAS}
%===========================
%{BindAdd 1}
%{BindAdd 2}
%{BindAdd 3}
%{Browse {RetrieveNodeSAS 1}}
%{Browse {Dictionary.entries SAS}}
%{UnifySAS 3 1}
%{Bindval 1 3}
%{Browse {RetrievefromSAS 3}}
%{Browse {Dictionary.entries SAS}}
%{Browse hello}
%=============================
%SAS finished

declare
Env={Dictionary.new}

declare
TotVar={NewCell 0}

declare
fun {GetID}
   %Function to generate a unique Environment variable for an identifier.
   TotVar:=@TotVar+1
   @TotVar
end

declare
fun {EnvMap Env X}
   %Function to return the environment variable for the identifier.
   %If it is not yet defined, then raise an exception
   if {Dictionary.member Env X}==false then raise varndec(X) end end
   %Return the mapped environment variable
   {Dictionary.get Env X}
end

declare
fun {ValMap Env V}
   %Function to map the identifiers in the value with the environment variables.
   %Need to take care of procedures here
   V
end

declare
proc {Run S E}
   {Browse S}
   {Browse {Dictionary.entries E}}
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
	 {BindAdd {Dictionary.get NE X}}
	 {Run S NE}
      end
   [] [bind ident(X) ident(Y)] then
      % Unify the two in the SAS
      {UnifySAS {EnvMap E X} {EnvMap E Y}}
   [] [bind ident(X) V] then
      {Bindval {EnvMap E X} {ValMap E V}}    
   [] [conditional ident(X) S1 S2] then
      local XSAS in
	 XSAS = {RetrievefromSAS {EnvMap E X}}
	 %To clarify
         case XSAS
	 of unBOUND then raise unbnd(X) end
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

%===========================
%Try Programs

try
   
{Run [localvar ident(x) [conditional ident(x) [nop] [nop]]] Env}

   %{Run [localvar ident(x) [ [localvar ident(x) [  [localvar ident(x) [nop]] [nop] [nop] ] ] [nop]  [nop]] ] Env}

   %{Run [localvar ident(x) [localvar ident(y) [bind ident(x) ident(y)]]] Env}

   %{Run [localvar ident(x) [localvar ident(y) [localvar ident(x) [localvar ident(y) [bind ident(x) ident(y)]]]]] Env}
catch Err then
   case Err
   of stmerr(X) then {Browse X} {Browse 'Above is not a statement. Error!!'}
   [] varndec(X) then {Browse X} {Browse 'Above identifier has not been declared. Error!!'}
   [] unbnd(X) then {Browse X} {Browse 'Above variable was unbound at time of usage.'}
                                %We do not have paraller programming for now, hence an error. 
   else {Browse 'Unidentified Exception!!'}
   end
finally
   {Browse 'Thank you for using our interpreter' }
end

%============================
