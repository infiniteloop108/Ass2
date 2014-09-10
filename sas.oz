%=============================================================================================
%Starting SAS
%SAS is a dictionary which maps environment variables to a 2-element list.
%1st element of that list contains the parent (in the Disjoint Set Data Structure). 2nd elemet signifies whether it is bound or unbound
%To see the status of a variable you have to look at its root.

%=============================================================================================
%Declare dictionary for SAS

declare
SAS = {Dictionary.new}

%=============================================================================================
%Add a new value to SAS

declare
proc {SASAdd X}
   {Dictionary.put SAS X [X unBOUND]}
end

%=============================================================================================
%Function for getting parent node in equivalence class

declare
fun {RetrieveNodeSAS Var}
   local Node in
      Node={Dictionary.get SAS Var}
      if Node.1==Var then Node
      else
	 %Path Compression
	 {Dictionary.put SAS Var {RetrieveNodeSAS Node.1}}
	 {Dictionary.get SAS Var}
      end
   end
end

%=============================================================================================
%Function for getting value of a variable

declare
fun {GetValFromSAS Var}
   local Node in
      Node={RetrieveNodeSAS Var}
      %Second element of the list
      Node.2.1
   end
end

%=============================================================================================
%Binding a variable to a value

declare
proc {BindVal Var Val}
   local Node in
      Node={RetrieveNodeSAS Var}
      case Node.2.1
      of unBOUND then {Dictionary.put SAS Node.1 [Node.1 Val]}
      else
	 if Node.2.1==Val then skip
	 else raise illass(Var) end
	 end
      end
   end
end

%=============================================================================================
%Unifying two variables

declare
proc {UnifySAS Var1 Var2}
   local NodeX NodeY in
      NodeX = {RetrieveNodeSAS Var1}
      NodeY = {RetrieveNodeSAS Var2}
      if NodeX.2.1==unBOUND then {Dictionary.put SAS NodeX.1 [NodeY.1 unBOUND]}
      else
	 if NodeY.2.1 == unBOUND then {Dictionary.put SAS NodeY.1 [NodeX.1 unBOUND]}
	 else
	    if NodeX.2.1 == NodeY.2.1 then
	       skip
	    else
	       raise illasseq(Var1 Var2) end
	    end
	 end
      end
   end
end

%SAS ends here
%=============================================================================================

{SASAdd 1}
{SASAdd 2}
{SASAdd 3}
{Browse {RetrieveNodeSAS 1}}
{Browse {Dictionary.entries SAS}}
{UnifySAS 3 1}
{BindVal 1 3}
{Browse {GetValFromSAS 3}}
{Browse {Dictionary.entries SAS}}
{Browse {GetValFromSAS 1}}

%=============================================================================================

