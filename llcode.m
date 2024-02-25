/*********************************************************************************************************
* This program aims to compute (l,l)-isogenies between a product of two elliptic curves and the Jacobian of 
  a genus 2 curve over a finite field of odd characteristic.          
*********************************************************************************************************/

/*********** (1)    formal   points     ******************/

/*
compute a formal point (x0+t, v(t)) on a (hyper)elliptic curve defined by an 
equation of the form y^2=f(x)
*/
function find_fp(H,x0,prec)
    K:=BaseRing(H);
    f:=HyperellipticPolynomials(H);
    b:=Evaluate(f,x0);
    LSR<t>:=LaurentSeriesRing(K,prec);
    R<y>:=PolynomialRing(LSR);
    if b eq 0 or not IsSquare(b) then
        
        while true do
              x1:=Random(K);
              b:=Evaluate(f,x1);
              if b ne 0 and IsSquare(b) then
                    return x1,  Roots(y^2-Evaluate(f,x1+t))[1][1];
              end if;
        end while;
    else

    return x0,  Roots(y^2-Evaluate(f,x0+t))[1][1];
    end if;
end function;




/* 
X,Y : (formal) points on an elliptic curve E of the form y^2=f(x)
compute X+Y
*/
function add_formal(E,X,Y)
    if Type(X[1]) ne RngSerLaurElt and Type(Y[1]) ne RngSerLaurElt then
         return E![X[1],X[2],X[3]]+ E![Y[1],Y[2],Y[3]];
    end if;
    if Type(Y[1]) eq RngSerLaurElt then
        if [X[1],X[2],X[3]] eq [0,1,0] then
        return Y;
        end if;
    elif Type(X[1]) eq RngSerLaurElt then
        if [Y[1],Y[2],Y[3]] eq [0,1,0] then
        return X;
        end if;  
    end if;
    a:=aInvariants(E);
    
    lambda:=(Y[2]-X[2])/(Y[1]-X[1]);
    x3:=lambda^2-Y[1]-X[1]-a[2];
    y3:=lambda*(X[1]-x3)-X[2];
    return [x3,y3,1];
end function;

function checkdeg(f,n)
	if Degree(f) le n then
	  return true;
	else
	  if #[i: i in [n+1..Degree(f)]|#Coefficients(Coefficient(f,i)) eq 0] eq (Degree(f)-n) then return true;  
	   else return false;
	  end if;
	end if;
end function;

function poly_reduce(f)
R:=Parent(f);
R0:=BaseRing(R);
a:=Coefficients(f);
b:=Monomials(f);
sum:=0;

for i in [1..#a] do
c:=Coefficients(a[i]);
if #c ne 0 then
sum+:=(R0!a[i])*b[i];
end if;
end for;
return sum;
end function;

/*
D1: [a1,b1], two polynomials defining a point on the Jacobian of a hyperelliptic curve
D2: [a2,b2]
f:  polynomial defining curve y^2=f
g: genus of the curve (g=2)
*/

function cantor_addition(D1,D2,f,g)

    a1,b1:=Explode(D1);
    a2,b2:=Explode(D2);
    a1:=poly_reduce(a1); b1:=poly_reduce(b1);
    a2:=poly_reduce(a2); b2:=poly_reduce(b2);

    d1,w1,w2:=XGCD(a1,a2);
    d,w3,u3:=XGCD(d1,b1+b2);
    u1:=w3*w1;u2:=w3*w2;

    a3:=a1*a2 div d^2; 
    a3:=poly_reduce(a3); 
    temp:=(u1*a1*(b2-b1)+u3*(f-b1^2)); 
    temp:=temp div d;
    b3:=b1+temp;
    b3:=b3 mod a3;       
    b3:=poly_reduce(b3);

    if checkdeg(a3,g) then
    return [poly_reduce(a3),poly_reduce(b3)];
    else
    a4:=a3;b4:=b3;
    a3:=(f-b3^2) div a3;
    Q,b3:=Quotrem(-b3, a3);

    while not checkdeg(a3,g) do
    t:=a4+Q*(b3-b4);
    b4:=b3;a4:=a3;a3:=t;
    Q,b3:=Quotrem(-b3, a3);

    end while;
    return [poly_reduce(a3),poly_reduce(b3)];
    end if;
end function;


/*
R1, R2: formal points on a genus 2 curve
P1: a formal point on an elliptic curve
return the scalars in the system of differential equations in gluing case. 
*/
function constants_in_SDE_gluing(R1,R2,P1)
    temp0:=Derivative(P1[1])/P1[2];
    temp1:=Derivative(R1[1])/R1[2];
    temp2:=Derivative(R2[1])/R2[2];
    a:=(temp1+temp2)/temp0;
    b:=(R1[1]*temp1+R2[1]*temp2)/temp0;
    return [Evaluate(a,0),Evaluate(b,0)];
end function;


function constants_in_SDE_generic(R1,R2,P)
    temp0:=Derivative(P[1])/P[2];
    temp1:=Derivative(R1[1])/R1[2];
    temp2:=Derivative(R2[1])/R2[2];
    a:=(temp1+temp2)/temp0;
    b:=(R1[1]*temp1+R2[1]*temp2)/temp0;
    m2:=(Coefficient(a,1)-Coefficient(a,0))/(Coefficient(P[1],1)-Coefficient(P[1],0));
    m1:=Coefficient(a,0)-m2*Coefficient(P[1],0);
    m4:=(Coefficient(b,1)-Coefficient(b,0))/(Coefficient(P[1],1)-Coefficient(P[1],0));
    m3:=Coefficient(b,0)-m4*Coefficient(P[1],0);

    return [m1,m2,m3,m4];
end function;

/*
PC: a formal point on a genus 2 curve
PE: a formal point on an elliptic curve
return the scalars in  the system of differential equations in splitting case. 
*/
function constants_in_SDE_splitting(PC,PE)
    temp0:=Derivative(PE[1])/PE[2];
    temp1:=Derivative(PC[1])/PC[2];
    temp2:=PC[1]*temp1;
    /* e0+e1*t+..=m1*(a0+a1*t+..)+ m2*(b0+b1*t+..)*/
    e0:=Coefficient(temp0,0);
    e1:=Coefficient(temp0,1);
    a0:=Coefficient(temp1,0);
    a1:=Coefficient(temp1,1);
    b0:=Coefficient(temp2,0);
    b1:=Coefficient(temp2,1);

    m1:=(b1*e0-b0*e1)/(b1*a0-b0*a1);
    m2:=(a1*e0-a0*e1)/(a1*b0-a0*b1);
    return [m1,m2];
end function;



/*
* R1,R2: formal points on genus 2 curve y^2=f(x)
* P1: formal point on the elliptic curve 
* m1,m2: scalars in differential equation
* f: the defining polynomial of curve y^2=f(x)
* 
*/
function increase_precision_gluing(R1,R2,P1,m1,m2,f,prec)

K:=Parent(m1);
LSR<t>:=LaurentSeriesRing(K,prec);
x1:=Coefficient(R1[1],0)+Coefficient(R1[1],1)*t;
y1:=Coefficient(R1[2],0)+Coefficient(R1[2],1)*t;
x2:=Coefficient(R2[1],0)+Coefficient(R2[1],1)*t;
y2:=Coefficient(R2[2],0)+Coefficient(R2[2],1)*t;

for d in [2..prec-1] do
    iy1:=1/y1;
    iy2:=1/y2;
    RR<x1d,x2d>:=PolynomialRing(K,2);
    sys:=[];
    
    sum1:=0; sum2:=0;
    dx1:=Derivative(x1);
    s1:=[Coefficient(dx1,i): i in [0..d-2]] cat [d*x1d];
    s2:=[Coefficient(iy1,i): i in [0..d-1]];
    sum1+:=&+[s1[i]*s2[d-i+1]:i in [1..d]];
    s1:=[Coefficient(x1*dx1,i): i in [0..d-2]] cat [Coefficient(x1*dx1,d-1)+d*x1d*Coefficient(x1,0)];
    sum2+:=&+[s1[i]*s2[d-i+1]:i in [1..d]];

    dx2:=Derivative(x2);
    s1:=[Coefficient(dx2,i): i in [0..d-2]] cat [d*x2d];
    s2:=[Coefficient(iy2,i): i in [0..d-1]];
    sum1+:=&+[s1[i]*s2[d-i+1]:i in [1..d]];
    s1:=[Coefficient(x2*dx2,i): i in [0..d-2]] cat [Coefficient(x2*dx2,d-1)+d*x2d*Coefficient(x2,0)];
    sum2+:=&+[s1[i]*s2[d-i+1]:i in [1..d]];
   
    temp:=Derivative(P1[1])/P1[2];
    sys cat:=[sum1-Coefficient(temp,d-1)*m1, sum2-Coefficient(temp,d-1)*m2];
    v:=Variety(ideal<RR|sys>)[1];
    
   
    x1+:=v[1]*t^d;
    x2+:=v[2]*t^d;

    y1d:=(Coefficient(&+[Coefficient(f,i)*x1^i: i in [0..5]],d)-Coefficient(y1^2,d))/(2*Coefficient(y1,0));
    y2d:=(Coefficient(&+[Coefficient(f,i)*x2^i: i in [0..5]],d)-Coefficient(y2^2,d))/(2*Coefficient(y2,0));
    
    y1+:=y1d*t^d;
    y2+:=y2d*t^d;

end for;
   return [[x1,y1],[x2,y2]];
end function;

/*
* R1,R2: formal points on genus 2 curve y^2=f(x)
* P: a formal point on the domian curve
* m1,m2,m3,m4: scalars in differential equation
* f: the defining polynomial of curve y^2=f(x)
*/
function increase_precision_generic(R1,R2,P,m1,m2,m3,m4,f,prec)

K:=Parent(m1);
LSR<t>:=LaurentSeriesRing(K,prec);
x1:=&+[Coefficient(R1[1],i)*t^i: i in [0..2]];
y1:=&+[Coefficient(R1[2],i)*t^i: i in [0..2]];
x2:=&+[Coefficient(R2[1],i)*t^i: i in [0..2]];
y2:=&+[Coefficient(R2[2],i)*t^i: i in [0..2]];

for d in [3..prec-1] do
    iy1:=1/y1;
    iy2:=1/y2;
    RR<x1d,x2d>:=PolynomialRing(K,2);
    sys:=[];
    
    sum1:=0; sum2:=0;
    dx1:=Derivative(x1);
    s1:=[Coefficient(dx1,i): i in [0..d-2]] cat [d*x1d];
    s2:=[Coefficient(iy1,i): i in [0..d-1]];
    sum1+:=&+[s1[i]*s2[d-i+1]:i in [1..d]];
    s1:=[Coefficient(x1*dx1,i): i in [0..d-2]] cat [Coefficient(x1*dx1,d-1)+d*x1d*Coefficient(x1,0)];
    sum2+:=&+[s1[i]*s2[d-i+1]:i in [1..d]];

    dx2:=Derivative(x2);
    s1:=[Coefficient(dx2,i): i in [0..d-2]] cat [d*x2d];
    s2:=[Coefficient(iy2,i): i in [0..d-1]];
    sum1+:=&+[s1[i]*s2[d-i+1]:i in [1..d]];
    s1:=[Coefficient(x2*dx2,i): i in [0..d-2]] cat [Coefficient(x2*dx2,d-1)+d*x2d*Coefficient(x2,0)];
    sum2+:=&+[s1[i]*s2[d-i+1]:i in [1..d]];
   
    temp1:=Derivative(P[1])/P[2];
    temp2:=P[1]*temp1;
    sys cat:=[sum1-Coefficient(temp1,d-1)*m1-Coefficient(temp2,d-1)*m2, sum2-Coefficient(temp1,d-1)*m3-Coefficient(temp2,d-1)*m4];
    v:=Variety(ideal<RR|sys>)[1];
    
   
    x1+:=v[1]*t^d;
    x2+:=v[2]*t^d;

    y1d:=(Coefficient(&+[Coefficient(f,i)*x1^i: i in [0..5]],d)-Coefficient(y1^2,d))/(2*Coefficient(y1,0));
    y2d:=(Coefficient(&+[Coefficient(f,i)*x2^i: i in [0..5]],d)-Coefficient(y2^2,d))/(2*Coefficient(y2,0));
    
    y1+:=y1d*t^d;
    y2+:=y2d*t^d;

end for;
   return [[x1,y1],[x2,y2]];
end function;

/*
* PE: formal points on the elliptic curve E
* PC: formal point on the hyperelliptic curve 
* m1,m2: scalars in differential equation
* fE: a polynomial defining the elliptic curve E: y^2=fE(x)
*/
function increase_precision_splitting(PE,PC,m1,m2,fE,prec)

K:=Parent(m1);
LSR<t>:=LaurentSeriesRing(K,prec);
xE:=Coefficient(PE[1],0)+Coefficient(PE[1],1)*t+Coefficient(PE[1],2)*t^2;
yE:=Coefficient(PE[2],0)+Coefficient(PE[2],1)*t++Coefficient(PE[2],2)*t^2;

temp0:=Derivative(PC[1])/PC[2];
RS:=m1*temp0+m2*PC[1]*temp0;


for d in [3..prec-1] do
    iyE:=1/yE;
    
    temp1:=[Coefficient(Derivative(xE),i):i in [0..d-2] ];
    temp2:=[Coefficient(iyE,i): i in [1..d-1]];

    sum:=&+[temp1[i]*temp2[d-i]: i in [1..d-1]];

    xd:=(Coefficient(RS,d-1)-sum)/(d*Coefficient(iyE,0));
    xE:=xE+xd*t^d;

    yd:=(Coefficient(&+[Coefficient(fE,i)*xE^i: i in [0..3]],d)-Coefficient(yE^2,d))/(2*Coefficient(yE,0));   
    yE+:=yd*t^d;
end for;
   return [xE,yE];
end function;



function rational_expr_reconstruct(s,u0)
    L:=[];
    ss:=s;

    R<t>:=Parent(s);
    K:=BaseRing(R);
    R0<x>:=FunctionField(K);

    if IsWeaklyZero(s) then 
    return R0!0;
    end if;

    while not IsWeaklyZero(s) do
        a,v,_:=Coefficients(s);
        if v le 0 then
            if #a le 1-v then
            s0:=&+[a[i]*t^(v+i-1):i in [1..#a]];
            L cat:=[&+[a[i]*(x-u0)^(v+i-1):i in [1..#a]]];
            else
            s0:=&+[a[i]*t^(v+i-1):i in [1..1-v]];
            L cat:=[&+[a[i]*(x-u0)^(v+i-1):i in [1..1-v]]];
            end if;
        s:=s-s0;
        else
        L cat:=[0];
        end if;
        if not IsWeaklyZero(s) then
        s:=1/s;
        end if;

    end while;


    case #L:
    when 1: result:=L[1];
    when 2: result:=L[1]+1/L[2];
    else
        f:=1/L[#L];
        for i in [1..#L-2] do
        f:=1/(f+L[#L-i]);
        end for;
        result:= L[1]+f;
    end case ;


    
    mp:=hom<R0->R|[u0+t]>;
    assert mp(result) eq ss;

    return result;
end function;


/*
* recover the four rational functions
*/
function expression(R1,R2,P1,x0)

      ss:=R1[1]+R2[1];
      pp:=R1[1]*R2[1];
      temp:=1/((R2[1]-R1[1])*P1[2]);
      qq:=(R2[2]-R1[2])*temp;
      rr:=(R1[2]*R2[1]-R2[2]*R1[1])*temp;

      SS:=rational_expr_reconstruct(ss,x0);
      PP:=rational_expr_reconstruct(pp,x0);
      QQ:=rational_expr_reconstruct(qq,x0);
      RR:=rational_expr_reconstruct(rr,x0);

      return [SS,PP,QQ,RR];

end function;




/********** (2)  Evaluation of Weil functions  ****************/


/****
f: a rational function on a curve C
P: a (formal) point on the curve C
return f(P)
****/

function evaluate(f,P)
N:=Numerator(f);
D:=Denominator(f);
R:=Parent(P[1]);

case Type(R):
    when FldFin:
	     if P[3] ne 0 then
			a:=P[1]/P[3];
			b:=P[2]/P[3];
			n:=Evaluate(N,[a,b]);
			d:=Evaluate(D,[a,b]);
			if d ne 0 then return n/d;
			elif n ne 0 then
			    return Infinity();
			else
				C:=Curve(Parent(f));
				F<x,y>:=FunctionField(C);
                                P:=C![P[1],P[2],P[3]];
                m:=Valuation(f,P );
                if m gt 0 then return 0;
                elif m lt 0 then return Infinity();
                else
                    m:=Valuation(Evaluate(N,[x,y]), P);
                    a:=Expand(x,Place(C!P):AbsPrec:=m+1);
				    b:=Expand(y,Place(C!P):AbsPrec:=m+1);
                    n:=Evaluate(N,[a,b]);
				    d:=Evaluate(D,[a,b]);
                    r:=Exponents(n/d); 
                    return Evaluate(n/d,0);
                end if;
			end if;
		 else
		    C:=Curve(Parent(f));
	        F<x,y>:=FunctionField(C);
            m:=Max({Valuation(Evaluate(N,[x,y]), P),Valuation(Evaluate(D,[x,y]), P)});
	        a:=Expand(x,Place(C!P):AbsPrec:=m+1);
	        b:=Expand(y,Place(C!P):AbsPrec:=m+1);
		    n:=Evaluate(N,[a,b]);
            d:=Evaluate(D,[a,b]);
			r:=Exponents(n/d); 
			 if #r eq 0 then
			    error "Error:  precision is not enough.";
			 elif r[1] lt 0 then return Infinity();			 
			 else
                 return Evaluate(n/d,0);			 
			 end if;
		 end if;
		 		
    when RngSerLaur:
	     a:=P[1]/P[3];
		 b:=P[2]/P[3];
		 n:=Evaluate(N,[a,b]);
		 d:=Evaluate(D,[a,b]);
		 if #Exponents(d) ne 0 then
	       return n/d;
		 else return Infinity();
		 end if;
end case;
end function;


/*
l: an odd prime
S: an l-torsion point on an elliptic curve E
T: a point on E
compute f_S(T)/f_S(-T), where f_S is a Miller function with divisor l(-S)-l(\infty).
*/
function double_and_add_elliptic(l,S,T)
    E:=Curve(S);
    if S eq E!0 then return 1;end if;
    if Type(T[1]) eq FldFinElt then
          T:=E![T[1],T[2],T[3]];
	  if S ne E!0 and T eq E!0 then return -1;end if;
            m:=Ilog2(l)-1;
	    a:=Intseq(l, 2);// l=a0+a1*2+...+a_m2^m+2^{m+1}
	    f:=1;
	    S:=-S; R:=S; 
            L:=[];

           test:=[];
            FF<x,y>:=FunctionField(E);
            while m ge 0 do
	    R2:=2*R;
	    _, g:=IsPrincipal(2*Divisor(Place(R))-Divisor(Place(R2))-Divisor(Place(E!0)));
	       if  R2 eq T or R2 eq -T or R eq -T then
                if  not IsDefined(L,1) then
                    LSR:=LaurentSeriesRing(Parent(T[1]),l);
                    fE:=HyperellipticPolynomials(E);
                    RRR:=PolynomialRing(LSR);
                    temp:=Roots(RRR.1^2- &+[Coefficient(fE,i)*(T[1]+LSR.1)^i: i in [0..3]])[1][1];
			        if Parent(T[1])!Evaluate(temp,0) ne T[2] then temp:=-temp;end if;
			        L:=[T[1]+LSR.1, temp,1];
                end if;	
            end if;
            if  IsDefined(L,1) then	     
                      f:=f^2*evaluate(g,L)/evaluate(g,[L[1], -L[2],L[3]]); 
            else
                     f:=f^2*evaluate(g,T)/evaluate(g,[T[1],-T[2],T[3]]); 
	       end if;    
	  
	    R:=R2;

	    if a[m+1] eq 1 then
		    RS:=R+S;
		    _, g:=IsPrincipal(Divisor(Place(R))+Divisor(Place(S))-Divisor(Place(RS))-Divisor(Place(E!0)));
                    if T eq RS or R eq -T or S eq -T or RS eq -T then
                             if  not IsDefined(L,1) then
                                LSR:=LaurentSeriesRing(Parent(T[1]),l);
                                fE:=HyperellipticPolynomials(E);
                                RRR:=PolynomialRing(LSR);
                                temp:=Roots(RRR.1^2- &+[Coefficient(fE,i)*(T[1]+LSR.1)^i: i in [0..3]])[1][1];
				                if Parent(T[1])!Evaluate(temp,0) ne T[2] then temp:=-temp;end if;
				                L:=[T[1]+LSR.1, temp,1];
                             end if;
                     end if;   
                         
                     if  IsDefined(L,1) then
                         f:=f*evaluate(g,L)/evaluate(g,[L[1], -L[2],L[3]]); 
                    else
                         f:=f*evaluate(g,T)/evaluate(g,[T[1],-T[2],T[3]]); 
                    end if;
		    
		    R:=RS;
	    end if;
	    m:=m-1;
	    end while;
	    if IsDefined(L,1) then 
		   return Parent(T[1])!Evaluate(f,0); 
   		else return f; end if;   
     else


	    m:=Ilog2(l)-1;
	    a:=Intseq(l, 2);// l=a0+a1*2+...+a_m2^m+2^{m+1}
	    f:=1;
	    S:=-S; R:=S; 

            while m ge 0 do
	    R2:=2*R;
	    _, g:=IsPrincipal(2*Divisor(Place(R))-Divisor(Place(R2))-Divisor(Place(E!0)));
	       
	    f:=f^2*evaluate(g,T)/evaluate(g,[T[1],-T[2],T[3]]); 
	    R:=R2;

	    if a[m+1] eq 1 then
		    RS:=R+S;
		    _, g:=IsPrincipal(Divisor(Place(R))+Divisor(Place(S))-Divisor(Place(RS))-Divisor(Place(E!0)));
		    f:=f*evaluate(g,T)/evaluate(g,[T[1],-T[2],T[3]]);
		    R:=RS;
	    end if;
	    m:=m-1;
	    end while;
	    return f;       
    end if;
   
    

   
end function;


/***
Q: mumford representation of  a point on Hyperelliptic Jacobian
***/
function JacPtToDivisor(Q)	
	H:=Curve(Parent(Q)); 
	if Q[3] eq 0 then
	assert Degree(Q[1]) eq 0;
	return DivisorGroup(H)!0;
	end if;
	F<x,y>:=FunctionField(H);
	D1:=Divisor(F!Q[1]);
	D2:=Divisor(y-F!Q[2]);
	E:=Numerator(GCD(D1,D2));
	assert Degree(E) eq Q[3];

	E:=E-Q[3]*Divisor(H![1,0,0]);
	assert JacobianPoint(Parent(Q),E) eq Q;
	return E;
end function;

/*
* f: a polynomial defining a genus curve H: y^2=f(x)
* l: an odd prime 
* S: an l-torsion point on Jac(H)
* T: a pair of polynomials defining a formal point on Jac(H)
* D24: a two-torsion defining the "theta" divisor
* return f_S(T)/f_S(-T)
*/
function double_and_add_g2(S,T,D24,l,f)
   
   if S eq Parent(S)!0 then return 1;end if;

        P<x>:=Parent(T[1]);
        temp:=[Coefficient(D24[1],2)*x^2+ Coefficient(D24[1],1)*x+Coefficient(D24[1],0), Coefficient(D24[2],1)*x+Coefficient(D24[2],0)];
        temp:=cantor_addition([T[1],T[2]],temp,f,2); 
        ii:=Roots(temp[1]); 

        H:=Curve(Parent(S));
        K:=BaseRing(H);
        if #ii eq 0 then
                K2:=ext<K|2>;
                RR0:=BaseRing(P);
                RR0:=ChangeRing(RR0,K2);
                Pext:=ChangeRing(P,RR0);
                ii:=Roots(Pext!temp[1]); 
                H2:=BaseChange(H,K2);
                R1:=[ii[1][1], Evaluate(temp[2],ii[1][1]),1 ];
                R2:=[ii[2][1], Evaluate(temp[2],ii[2][1]),1 ]; 
                R1z:=H2![K2!Evaluate(i,0): i in R1];
                R2z:=H2![K2!Evaluate(i,0): i in R2];
        else
                R1:=[ii[1][1], Evaluate(temp[2],ii[1][1]),1 ];
                R2:=[ii[2][1], Evaluate(temp[2],ii[2][1]),1 ]; 
                R1z:=H![K!Evaluate(i,0): i in R1];
                R2z:=H![K!Evaluate(i,0): i in R2];
        end if;
        
        if &and[Parent(R1[i])!R1z[i] eq R1[i]: i in [1,2,3]] then
           temp:=R1; R1:=R2;R2:=temp;
           temp:=R1z;R1z:=R2z;R2z:=temp;
        end if;

        if &and[Parent(R2[i])!R2z[i] eq R2[i]: i in [1,2,3]] then
           R2:=R2z;
        end if;


       // FF<x,y>:=FunctionField(H);
            S1:=-S;
            D:=JacPtToDivisor(S1)+2*Divisor(H![1,0,0]);
            temp0:=Basis(D);
            temp:=Divisor(temp0[1])+D+Divisor(H![1,0,0]);
            f2,f1:=Explode(Basis(temp));

            if f1 ne Parent(f1)!1 then
                f2:=f1;
            end if;


 
            t1:=(evaluate(f2,R1)-evaluate(f2,R2))/(evaluate(f2,[R1[1],-R1[2],1])-evaluate(f2,[R2[1],-R2[2],1]));
            t1:=t1^l;
            t2:=1; t3:=1;

    m:=Ilog2(l)-1;
    a:=Intseq(l, 2);
    S2:=S1;

    L2:=[];

    while m ge 0 do
        S22:=2*S2;
        _,g:=IsPrincipal(2*JacPtToDivisor(S2)-JacPtToDivisor(S22));
        t2:=t2^2*evaluate(g,R1)/evaluate(g,[R1[1],-R1[2],1]);
        
         if IsDefined(L2,1) then
                temp1:=evaluate(g,L2);
                temp2:=evaluate(g,[L2[1],-L2[2],L2[3]]);
            else
                temp1:=evaluate(g,R2);
                temp2:=evaluate(g,[R2[1],-R2[2],R2[3]]);

                if Type(temp1) eq Infty or Type(temp2) eq Infty or temp2 eq 0  then
                            L2:=FormalPoint(R2);
                            L2:=[L2[1],L2[2],L2[3]];
                            temp1:=evaluate(g,L2);
                            temp2:=evaluate(g,[L2[1],-L2[2],L2[3]]);  
                end if;
            end if;
        t3:=t3^2*temp1/temp2; 
        S2:=S22;
        
        if a[m+1] eq 1 then
          S1S2:=S2+S1;
           _,g:=IsPrincipal(JacPtToDivisor(S2)+JacPtToDivisor(S1)-JacPtToDivisor(S1S2));
           t2:=t2*evaluate(g,R1)/evaluate(g,[R1[1],-R1[2],1]);
           
            if IsDefined(L2,1) then
                temp1:=evaluate(g,L2);
                temp2:=evaluate(g,[L2[1],-L2[2],L2[3]]);
            else
                temp1:=evaluate(g,R2);
                temp2:=evaluate(g,[R2[1],-R2[2],R2[3]]);

                if Type(temp1) eq Infty or Type(temp2) eq Infty or temp2 eq 0  then
                            L2:=FormalPoint(R2);
                            RR:=Parent(L2[1]);
                            RR:=ChangeRing(RR,Parent(R1[1]));
                            L2:=[RR!L2[1],RR!L2[2],RR!L2[3]];
                            temp1:=evaluate(g,L2);
                            temp2:=evaluate(g,[L2[1],-L2[2],L2[3]]);
                end if;
            end if;
           t3:=t3*temp1/temp2;
           S2:=S1S2;
        end if;
        m:=m-1;
    end while;

       if IsDefined(L2,1) then 
         return   BaseRing(P)!(t1*t2*Evaluate(t3,0));
         else
          return BaseRing(P)!(t1*t2*t3);
        end if;
    
    
end function;







function trace(a,qq,t)
temp:=a;
sum:=a;
i:=1;
while i lt t do
temp:=temp^qq;
sum+:=temp;
i+:=1;
end while;
return sum;
end function;


/*
* f: a polynomial defining a genus curve H: y^2=f(x)
* T: a pair of polynomials defining a (formal) point on Jac(H)
* kerV: isogeny kernel in a certain form 
* D24: a two-torsion defining the "theta" divisor
* l: an odd prime 
* qq: the size of a field over which Weil funcs for 2-torsion points are rational
* return \tilde{\theta}(T) in the paper
*/
function invariant_section(kerV,T,D24,l,qq,f)
   sum:=0;
   P<x>:=Parent(T[1]); 
   H:=Curve(Parent(D24));
   K:=BaseRing(P);
   
   assert Type(T) eq JacHypPt;

  

      for S in kerV do
         temp:=S[1]+D24+T;
         L1:=[]; L2:=[]; // formal points R1 and R2
        if Degree(temp[1]) eq 0 then
            L1:=FormalPoint(H![1,0,0]);
            L2:=Parent(L1)![Evaluate(L1[1],2*Parent(L1[1]).1),Evaluate(L1[2],2*Parent(L1[1]).1),Evaluate(L1[3],2*Parent(L1[1]).1)];
            L1:=[L1[1],L1[2],L1[3]];L2:=[L2[1],L2[2],L2[3]];
        elif Degree(temp[1]) eq 1 then
            ii:=Roots(temp[1]);
            R1:=H![ii[1][1],Evaluate(temp[2],ii[1][1]),1];
            L2:=FormalPoint(H![1,0,0]);L2:=[L2[1],L2[2],L2[3]];
        else
            ii:=Roots(temp[1]);
            if #ii eq 1 then
                L1:=FormalPoint(H![ii[1][1],Evaluate(temp[2],ii[1][1]),1]);
                L2:=Parent(L1)![Evaluate(L1[1],2*Parent(L1[1]).1),Evaluate(L1[2],2*Parent(L1[1]).1),Evaluate(L1[3],2*Parent(L1[1]).1)];
                L1:=[L1[1],L1[2],L1[3]];L2:=[L2[1],L2[2],L2[3]];
            elif #ii eq 2 then
                R1:=H![ii[1][1],Evaluate(temp[2],ii[1][1]),1];
                R2:=H![ii[2][1],Evaluate(temp[2],ii[2][1]),1];
            else
                K2:=ext<K|2>;
                ii:=Roots(temp[1],K2); 
                H2:=BaseChange(H,K2);
                if #ii eq 1 then
                  L1:=FormalPoint(H2![K2!ii[1][1],K2!Evaluate(temp[2],ii[1][1]),1]);
                  L2:=Parent(L1)![Evaluate(L1[1],2*Parent(L1[1]).1),Evaluate(L1[2],2*Parent(L1[1]).1),Evaluate(L1[3],2*Parent(L1[1]).1)];
                  L1:=[L1[1],L1[2],L1[3]];L2:=[L2[1],L2[2],L2[3]];
                else
                    R1:=H2![ii[1][1],Evaluate(temp[2],ii[1][1]),1];
                    R2:=H2![ii[2][1],Evaluate(temp[2],ii[2][1]),1];
                end if;
            end if;
        end if;

            S0:=-S[1];
            D:=JacPtToDivisor(S0)+2*Divisor(H![1,0,0]);
            temp0:=Basis(D);
            temp:=Divisor(temp0[1])+D+Divisor(H![1,0,0]);
            f2,f1:=Explode(Basis(temp));  
            if f1 ne Parent(f1)!1 then
                //assert f2 eq Parent(f1)!1;
                f2:=f1;
            end if;
            
           if IsDefined(L1,1) then
                temp1:=evaluate(f2,L1);
                temp3:=evaluate(f2,[L1[1],-L1[2],L1[3]]);
          else
                temp1:=evaluate(f2,R1);
                temp3:=evaluate(f2,[R1[1],-R1[2],R1[3]]);

                if &or[Type(i) eq Infty: i in [temp1,temp3]] then
                            L1:=FormalPoint(R1);
                            L1:=[L1[1],L1[2],L1[3]];
                            temp1:=evaluate(f2,L1);
                            temp3:=evaluate(f2,[L1[1],-L1[2],L1[3]]);
                end if;
           end if;

           if IsDefined(L2,1) then
                temp2:=evaluate(f2,L2);
                temp4:=evaluate(f2,[L2[1],-L2[2],L2[3]]);
          else
                temp2:=evaluate(f2,R2);
                temp4:=evaluate(f2,[R2[1],-R2[2],R2[3]]);

                if &or[Type(i) eq Infty: i in [temp2,temp4]] then
                        L2:=FormalPoint(R2);
                        L2:=[L2[1],L2[2],L2[3]];
                        temp2:=evaluate(f2,L2);
                        temp4:=evaluate(f2,[L2[1],-L2[2],L2[3]]);  
                end if;
          end if;

          t1:=(temp1-temp2)/(temp3-temp4); 
          t1:=t1^l;
          t2:=1; t3:=1;

          m:=Ilog2(l)-1;
          a:=Intseq(l, 2);
          S1:=S0;
          
          while m ge 0 do
            S1S1:=2*S1;
            _,g:=IsPrincipal(2*JacPtToDivisor(S1)-JacPtToDivisor(S1S1));

           if IsDefined(L1,1) then
            temp1:=evaluate(g,L1);
            temp2:=evaluate(g,[L1[1],-L1[2],L1[3]]);
           else
            temp1:=evaluate(g,R1);
            temp2:=evaluate(g,[R1[1],-R1[2],R1[3]]);

                if Type(temp1) eq Infty or Type(temp2) eq Infty or temp2 eq 0  then
                            L1:=FormalPoint(R1);
                            L1:=[L1[1],L1[2],L1[3]];
                            temp1:=evaluate(g,L1);
                            temp2:=evaluate(g,[L1[1],-L1[2],L1[3]]);
                end if;
           end if;
           t2:=t2^2*temp1/temp2; 

            if IsDefined(L2,1) then
                temp1:=evaluate(g,L2);
                temp2:=evaluate(g,[L2[1],-L2[2],L2[3]]);
            else
                temp1:=evaluate(g,R2);
                temp2:=evaluate(g,[R2[1],-R2[2],R2[3]]);

                if Type(temp1) eq Infty or Type(temp2) eq Infty or temp2 eq 0  then
                            L2:=FormalPoint(R2);
                            L2:=[L2[1],L2[2],L2[3]];
                            temp1:=evaluate(g,L2);
                            temp2:=evaluate(g,[L2[1],-L2[2],L2[3]]);
                end if;
            end if;
            t3:=t3^2*temp1/temp2;
            S1:=S1S1;
        
            if a[m+1] eq 1 then
                 S1S0:=S1+S0;
                  _,g:=IsPrincipal(JacPtToDivisor(S1)+JacPtToDivisor(S0)-JacPtToDivisor(S1S0));
                if IsDefined(L1,1) then
                        temp1:=evaluate(g,L1);
                        temp2:=evaluate(g,[L1[1],-L1[2],L1[3]]);
                        else
                        temp1:=evaluate(g,R1);
                        temp2:=evaluate(g,[R1[1],-R1[2],R1[3]]);

                            if Type(temp1) eq Infty or Type(temp2) eq Infty or temp2 eq 0  then
                                        L1:=FormalPoint(R1);
                                        L1:=[L1[1],L1[2],L1[3]];
                                        temp1:=evaluate(g,L1);
                                        temp2:=evaluate(g,[L1[1],-L1[2],L1[3]]);
                            end if;
                end if;
                t2:=t2*temp1/temp2;
      
                if IsDefined(L2,1) then
                    temp1:=evaluate(g,L2);
                    temp2:=evaluate(g,[L2[1],-L2[2],L2[3]]);
                    else
                    temp1:=evaluate(g,R2);
                    temp2:=evaluate(g,[R2[1],-R2[2],R2[3]]);

                        if Type(temp1) eq Infty or Type(temp2) eq Infty or temp2 eq 0  then
                                    L2:=FormalPoint(R2);
                                    L2:=[L2[1],L2[2],L2[3]];
                                    temp1:=evaluate(g,L2);
                                    temp2:=evaluate(g,[L2[1],-L2[2],L2[3]]);
                        end if;
                end if;          
                t3:=t3*temp1/temp2;
                S1:=S1S0;
        end if;
        m:=m-1;
    end while;
         if IsDefined(L1,1) or IsDefined(L2,1) then         
           sum+:=trace(K!Evaluate(t1*t2*t3,0),qq,S[2]);
         else
           sum+:= trace(K!(t1*t2*t3),qq,S[2]);
        end if;
      end for;
        return sum;
 


end function;


/*
* i,j: denote the function eta_{ij} in the paper, i<j
* T: [x^2+a1*x+a0, b1*x+b0]
* mu  : roots of the defining polynomial
* return eta_{ij}((x1,y1),(x2,y2)), where x1,x2 are roots of x^2+a1*x+a0, b1*x1+b0=y1, b1*x2+b0=y2
*/
function evaluate_eta(i,j,T,mu)
    x1x2:=Coefficient(T[1],0);
    x1px2:=-Coefficient(T[1],1);
    
    if i eq 0 then
        return x1x2-mu[j]*x1px2+mu[j]^2;
    else
       y1y2:=Coefficient(T[2],1)^2*x1x2+Coefficient(T[2],1)*Coefficient(T[2],0)*x1px2+Coefficient(T[2],0)^2;
       temp:=x1px2^2-4*x1x2;
       
       s:=[k: k in {1..5} diff {i,j}];
       a2:=-&+[mu[k]: k in s];
       a1:=mu[s[1]]*mu[s[2]]+mu[s[1]]*mu[s[3]]+mu[s[3]]*mu[s[2]];
       a0:=-&*[mu[k]: k in s];
       b1:=-(mu[i]+mu[j]);
       b0:=mu[i]*mu[j];

      return  (-2*y1y2+b0*x1px2^3 + b1*x1px2^2*x1x2 + (a2*b0 + a0)*x1px2^2 + x1px2*x1x2^2 + (a2*b1 + a1 -
    3*b0)*x1px2*x1x2 + (a1*b0 + a0*b1)*x1px2 + (2*a2 - 2*b1)*x1x2^2 + (-2*a2*b0 +
    2*a1*b1 - 2*a0)*x1x2 + 2*a0*b0)/temp;
    end if;

end function;

/***********************(3) gluing case ***************************************/

function orbit(S,K)
q:=#K;
E1:=Curve(S[1]); E2:=Curve(S[2]); 
T1:=S[1]; T2:=S[2];
temp:=[];
repeat 
T1:=E1![T1[1]^q,T1[2]^q, T1[3]^q]; 
T2:=E2![T2[1]^q,T2[2]^q, T2[3]^q]; 
temp cat:=[<T1,T2>];
until T1 eq S[1] and T2 eq S[2];

return temp;
end function;


function representaion_of_kernel(G,l,K)

total:={<i*G[1][1]+j*G[2][1], i*G[1][2]+j*G[2][2]>: i in [0..l-1], j in [0..l-1]};
V:=[];
while #total gt 0 do
temp:=orbit(Rep(total),K);
V cat:=[<Rep(temp),#temp>];
total:=total diff {i: i in temp};
end while;
m:=(l+1) div 2;
return [<<m*i[1][1],m*i[1][2]>, i[2]> : i in V];
end function;

/*
* H: a genus 2 curve over K
* return a quadratic twist of $H$ whose Jacobian is isogenous to E1 x E2.
*/
function is_isogenous(LP,K,H)
    R<x>:=PolynomialRing(K);
    f,_:=HyperellipticPolynomials(H);
    J:=Jacobian(H);

    N:=Evaluate(LP,1);
    for i in [1,2] do
    P:=Random(J);
    if N*P ne J!0 then
      return QuadraticTwist(H);
    end if;
    end for;

    if LP eq LPolynomial(H) then
    return H;
    else
    return QuadraticTwist(H);
    end if;
end function;


/*
C1, C2: genus 2 curves
S: a sequence of points on C1
return the images of points in S under an isomorphism from C1 to C2 
*/
function image_under_isomorphism(C1,C2,S)
    _, f:=IsIsomorphic(C1, C2);
    f:=DefiningPolynomials(f); 
    r:=[];
    for s in S do
    t:=[Evaluate(f[i],[s[1],s[2],s[3]]): i in [1,2,3]];
    r cat:=[[t[1]/t[3],t[2]/t[3]^3,1]];
    end for;
    return r;
end function;

/*
* s1: [a0+b0, a1+b1, a2+b2] 
* s2: [a0*b0, a0*b1+a1*b0, a0*b2+a1*b1+a2*b0] 
* return [a0+a1*t+a2*t^2+O(t^3), *],[b0+b1*t+b2*t^2+O(t^3), *]
*/
function find_root(y1y2test,s1,s2,mu)
K:=Parent(s1[1]);
R<x>:=PolynomialRing(K);
a0,b0:=Explode([i: i in {*i[1]^^i[2]: i in Roots(x^2-s1[1]*x+s2[1])*}]);

a1:=(a0*s1[2]-s2[2])/(a0-b0);
b1:=s1[2]-a1;

if #s1 eq 3 then
a2:=(a0*s1[3]-s2[3]+a1*b1)/(a0-b0);
b2:=s1[3]-a2;

LSR:=Parent(y1y2test);
x1:=a0+a1*LSR.1+a2*LSR.1^2;
x2:=b0+b1*LSR.1+b2*LSR.1^2;


R<y>:=PolynomialRing(LSR);
y1:=Roots(y^2-&*[x1-mu[i]: i in [1..5]])[1][1];
y2:=Roots(y^2-&*[x2-mu[i]: i in [1..5]])[1][1];


test:=(x2-mu[1])*(x2-mu[2])*(x1-mu[3])*(x1-mu[4])*(x1-mu[5])+(x1-mu[1])*(x1-mu[2])*(x2-mu[3])*(x2-mu[4])*(x2-mu[5])+(x1-x2)^2*y1y2test;

if test eq 2*y1*y2 then
  return [x1,y1],[x2,y2];

else 
  assert test eq -2*y1*y2;
return [x1,y1],[x2,-y2];
end if;

end if;

if #s1 eq 2 then
  LSR:=Parent(y1y2test);
  x1:=a0+a1*LSR.1;
  x2:=b0+b1*LSR.1;
  R<y>:=PolynomialRing(LSR);
  y1:=Roots(y^2-&*[x1-mu[i]: i in [1..5]])[1][1];
  y2:=Roots(y^2-&*[x2-mu[i]: i in [1..5]])[1][1];
  test:=(x2-mu[1])*(x2-mu[2])*(x1-mu[3])*(x1-mu[4])*(x1-mu[5])+(x1-mu[1])*(x1-mu[2])*(x2-mu[3])*(x2-mu[4])*(x2-mu[5])+ (x1-x2)^2*y1y2test;
  
    if test eq 2*y1*y2 then
       return [x1,y1],[x2,y2];
    else 
       assert test eq -2*y1*y2;
       return [x1,y1],[x2,-y2];
    end if;
end if;
end function;

function evaluate_phi(phi1,phi2,J,P1P2)
  R<x>:=Parent((J!0)[1]);
  K:=BaseRing(J);
  temp:=[K!Evaluate(i,P1P2[1][1]): i in phi1];
  first:=J![x^2-temp[1]*x+temp[2],(temp[3]*x+temp[4])*K!P1P2[1][2]];

  temp:=[K!Evaluate(i,P1P2[2][1]): i in phi2];
  second:=J![x^2-temp[1]*x+temp[2],(temp[3]*x+temp[4])*K!P1P2[2][2]];

  return first+second;
end function;

/*
* G: two points on E1 x E2 which generate a maximal isotropic subgroup of l-torsion group w.r.t. the Weil pairing associated to the product polarization
*/
declare verbose llisogeny,1;
intrinsic GluingIsogeny(E1::CrvEll, E2::CrvEll, G:: SeqEnum, l:: RngIntElt)-> CrvHyp, Tup
{Return a curve whose Jacobian is (E1 times E2)/G}
require IsWeierstrassModel(E1) and IsWeierstrassModel(E2): "Argument 1 or 2 is not in Weierstrass Model";
require BaseRing(E1) eq BaseRing(E2): "Argument 1 and 2 are not over the same field";
require IsPrime(l) and (l gt 2): "Argument 4 is not an odd prime";

K0:=BaseRing(E1);
f1:=HyperellipticPolynomials(E1);
f2:=HyperellipticPolynomials(E2);
K1:=SplittingField({f1,f2});
E1ext:=BaseChange(E1,K1);
E2ext:=BaseChange(E2,K1);

Q11,Q12,Q13:=Explode([i: i in DivisionPoints(E1ext!0, 2)| i ne E1ext!0]);
Q21,Q22,Q23:=Explode([i: i in DivisionPoints(E2ext!0, 2)| i ne E2ext!0]);

vprint llisogeny:"-- a symplectic basis ---\n", 
"(Q11,0)=", <Q11,E2!0>, "\n",
"(0,Q21)=", <E1!0,Q21>, "\n",
"(Q12,0)=", <Q12,E2!0>, "\n",
"(0,Q22)=", <E1!0,Q22>, "\n\n"; 

alpha1:=(Q11[1]-Q13[1])/(Q11[1]-Q12[1]);
beta1:=(Q12[1]-Q13[1])/(Q12[1]-Q11[1]);
alpha2:=(Q21[1]-Q23[1])/(Q21[1]-Q22[1]);
beta2:=(Q22[1]-Q23[1])/(Q22[1]-Q21[1]);

if not &and[IsSquare(i): i in [alpha1,beta1,alpha2,beta2]] then
K1:=ext<K1|2>;// printf "MinimalPolynomial(K1.1,K0)=%o\n\n",MinimalPolynomial(K1.1,K0); 
end if;

alpha1:=Sqrt(K1!alpha1);
beta1:=Sqrt(K1!beta1);
alpha2:=Sqrt(K1!alpha2);
beta2:=Sqrt(K1!beta2);

vprint llisogeny:"alpha1=",alpha1, "  beta1=", beta1,"\n";
vprint llisogeny:"alpha2=",alpha2, "  beta2=", beta2,"\n";

qq:=#K1;

kerV:=representaion_of_kernel(G,l,K1);

extdeg:=LCM([Degree(BaseRing(Curve(G[1][1])),K0), Degree(BaseRing(Curve(G[1][2])),K0), Degree(BaseRing(Curve(G[2][1])),K0),Degree(BaseRing(Curve(G[2][2])),K0),
Degree(K1,K0)]);
K:=ext<K0|extdeg>; Embed(K1,K); Embed(BaseRing(Curve(G[1][1])),K); // printf "MinimalPolynomial(K.1,K0)=%o\n\n",MinimalPolynomial(K.1,K0); 
E1ext:=BaseChange(E1,K);
E2ext:=BaseChange(E2,K); 

h0:=AssociativeArray();
for ii in [[0,1,0,0],[0,0,0,1],[1,0,0,0],[1,1,0,0],[1,0,0,1],[0,0,1,0]] do
    sum1:=0; sum2:=0;
    for S in kerV do
    T1:=E1ext![S[1][1][1],S[1][1][2],S[1][1][3]]+ E1ext!Q13; T2:=E2ext![S[1][2][1],S[1][2][2],S[1][2][3]]+E2ext!Q23;
    T3:=T1+E1ext!(ii[1]*Q11+ii[3]*Q12); T4:=T2+E2ext!(ii[2]*Q21+ii[4]*Q22); 

    t1t2:=double_and_add_elliptic(l,E1ext!S[1][1],T1)*double_and_add_elliptic(l,E2ext!S[1][2],T2);
    t3t4:=double_and_add_elliptic(l,E1ext!S[1][1],T3)*double_and_add_elliptic(l,E2ext!S[1][2],T4);

    sum1+:=&+[t1t2^(qq^i): i in [0..S[2]-1]];
    sum2+:=&+[t3t4^(qq^i): i in [0..S[2]-1]];
    end for;
    temp1:= ([ii[1],ii[3]] eq [0,0]) select 1 else ii[1]*alpha1+ii[3]*beta1;
    temp2:= ([ii[2],ii[4]] eq [0,0]) select 1 else ii[2]*alpha2+ii[4]*beta2;

   h0[ii]:=(temp1*temp2)^l*(sum2/sum1)^2;

   if h0[ii] eq 0 then
      error "Error: it is not a gluing isogeny. No implementation.\n";
   end if;
end for;

mu3:=h0[[0,1,0,0]]/(h0[[1,0,0,0]]*h0[[1,1,0,0]]);
mu4:=h0[[0,0,0,1]]*h0[[0,1,0,0]]/(h0[[1,0,0,1]]*h0[[1,1,0,0]]);
mu5:=h0[[0,0,0,1]]/(h0[[1,0,0,0]]*h0[[1,0,0,1]]);
vprint llisogeny:"mu3=",mu3, "mu4=", mu4, "mu5=", mu5,"\n";
R<x>:=PolynomialRing(K1);
H0:=HyperellipticCurve(x*(x-1)*(x-mu3)*(x-mu4)*(x-mu5));
if Genus(H0) ne 2 then
    error "Error: it is not a gluing isogeny. No implementation.\n";
end if;

//invariants:=IgusaInvariants(H0:normalize:=true);
//H:=HyperellipticCurveFromIgusaInvariants([K0!i: i in invariants]); 
//H:=HasOddDegreeModel(H);
//H:=is_isogenous(LPolynomial(E1)*LPolynomial(E2),K0,H);
H:=H0;

if Characteristic(K) lt (3*l+1) then
printf "No implementation for the algebraic form of isogeny.\n";
return H, _;
else

// compute Ei->E1 x E2 ->(E1 x E2)/G = Jac(H0)

LSR<t>:=LaurentSeriesRing(K,2);
u1,v1:=find_fp(E1ext,9,2);
vprint llisogeny: "-- formal point on E1 --\n";
vprint llisogeny: "u1=", u1+t, "v1=",v1,"\n";
a1:=AssociativeArray();
u2,v2:=find_fp(E2ext,1,2);v2:=-v2;
vprint llisogeny: "-- formal point on E2 --\n";
vprint llisogeny: "u2=", u2+t, "v2=",v2,"\n";
a2:=AssociativeArray();

A1:=E1ext!Q13+E1ext!G[1][1]; // here we assume that G[1][1] is not the identity.
A2:=add_formal(E1ext,A1,[u1+t,v1]);
B1:=E2ext!Q23+E2ext!G[1][2];
B2:=add_formal(E2ext,B1,[u2+t,v2]);
sum1:=0; sum2:=0;
for S in kerV do
    T:=add_formal(E1ext,A2,S[1][1]); temp:=double_and_add_elliptic(l,E1ext!S[1][1],T);
    T:=add_formal(E2ext,B1, S[1][2]); temp:=temp*double_and_add_elliptic(l,E2ext!S[1][2],T);
    sum1+:=&+[trace(Coefficient(LSR!temp,j),qq,S[2])*t^j: j in [0,1]];
    T:=add_formal(E1ext,A1,S[1][1]); temp:=double_and_add_elliptic(l,E1ext!S[1][1],T);
    T:=add_formal(E2ext,B2, S[1][2]); temp:=temp*double_and_add_elliptic(l,E2ext!S[1][2],T);
    sum2+:=&+[trace(Coefficient(LSR!temp,j),qq,S[2])*t^j: j in [0,1]];
end for;

for ii in [[1,0,0,0],[0,0,1,0],[1,0,1,0]] do
   sum3:=0; sum4:=0;
   for S in kerV do
      T:=add_formal(E1ext,A2,E1ext!S[1][1]+ii[1]*E1ext!Q11+ii[3]*E1ext!Q12); 
      temp:=double_and_add_elliptic(l,E1ext!S[1][1],T);
      T:=add_formal(E2ext,B1, S[1][2]); temp:=temp*double_and_add_elliptic(l,E2ext!S[1][2],T);
      sum3+:=&+[trace(Coefficient(LSR!temp,j),qq,S[2])*t^j: j in [0,1]];
      
      T:=add_formal(E1ext,A1,E1ext!S[1][1]+ii[1]*E1ext!Q11+ii[3]*E1ext!Q12); 
      temp:=double_and_add_elliptic(l,E1ext!S[1][1],T);
      T:=add_formal(E2ext,B2, S[1][2]); temp:=temp*double_and_add_elliptic(l,E2ext!S[1][2],T);
      sum4+:=&+[trace(Coefficient(LSR!temp,j),qq,S[2])*t^j: j in [0,1]];  
   end for;
    temp:= add_formal(E1ext, [u1+t,v1], G[1][1]);
     if [ii[1],ii[3]] eq [1,0] then
      temp1:=alpha1*(temp[1]-Q12[1])/(temp[1]-Q13[1]);
      temp2:=alpha1*(G[1][1][1]-Q12[1])/(G[1][1][1]-Q13[1]);
    elif [ii[1],ii[3]] eq [0,1] then
      temp1:=beta1*(temp[1]-Q11[1])/(temp[1]-Q13[1]);
      temp2:=beta1*(G[1][1][1]-Q11[1])/(G[1][1][1]-Q13[1]);
    else
       temp1:=alpha1*beta1*(Q12[1]-Q11[1])/(temp[1]-Q13[1]);
       temp2:=alpha1*beta1*(Q12[1]-Q11[1])/(G[1][1][1]-Q13[1]);
    end if;

    a1[ii]:=temp1^l*(sum3/sum1)^2;
   
    a2[ii]:=temp2^l*(sum4/sum2)^2;
end for;

t1:=mu4/h0[[1,0,0,0]];
t2:=mu4*(mu3-1)*(mu5-1)/h0[[0,0,1,0]];
t3:=t2/(mu3*mu5*h0[[1,0,0,0]]);
x1x2:=t1*a1[[1,0,0,0]];
x1px2:=x1x2+1+t3*a1[[1,0,1,0]];
y1y2test:=t2*a1[[0,0,1,0]];

// temp1+temp2 -mu2-mu4 sim R1+R2 -2infty 
// to do: here temp1 and temp2 could be not rational, we can work on a quadratic extension or try another formal point  
temp1,temp2:=find_root(y1y2test,[Coefficient(x1px2,i):i in [0,1]],[Coefficient(x1x2,i):i in [0,1]],[0,1,mu3,mu4,mu5]);

RRR<X>:=PolynomialRing(LSR);
temp:=cantor_addition([(X-temp1[1])*(X-temp2[1]), X*(temp2[2]-temp1[2])/(temp2[1]-temp1[1])+(temp1[2]*temp2[1]-temp2[2]*temp1[1])/(temp2[1]-temp1[1])],
[(X-1)*(X-mu4),0],X*(X-1)*(X-mu3)*(X-mu4)*(X-mu5),2);
R1,R2:=Explode([[i[1],Evaluate(temp[2],i[1]),1]: i in Roots(temp[1])]);


x1x2:=t1*a2[[1,0,0,0]];
x1px2:=x1x2+1+t3*a2[[1,0,1,0]];
y1y2test:=t2*a2[[0,0,1,0]];
temp1,temp2:=find_root(y1y2test,[Coefficient(x1px2,i):i in [0,1]],[Coefficient(x1x2,i):i in [0,1]],[0,1,mu3,mu4,mu5]);
temp:=cantor_addition([(X-temp1[1])*(X-temp2[1]), X*(temp2[2]-temp1[2])/(temp2[1]-temp1[1])+(temp1[2]*temp2[1]-temp2[2]*temp1[1])/(temp2[1]-temp1[1])],
[(X-1)*(X-mu4),0],X*(X-1)*(X-mu3)*(X-mu4)*(X-mu5),2);
R3,R4:=Explode([[i[1],Evaluate(temp[2],i[1]),1]: i in Roots(temp[1])]);

R1,R2,R3,R4:=Explode(image_under_isomorphism(H0,BaseChange(H,K1),[R1,R2,R3,R4]));

vprint llisogeny:"-- image of the formal point on E1 --\n";
vprint llisogeny:"R1=",R1,"\n","R2=",R2,"\n";
vprint llisogeny:"-- image of the formal point on E2 --\n";
vprint llisogeny:"R3=",R3,"\n","R4=",R4,"\n";
m1,m2:=Explode(constants_in_SDE_gluing(R1,R2,[u1+t,v1]));
vprint llisogeny: "m1=",m1, "m2=",m2,"\n";
prec:=3*l+1;
LSR<t>:=LaurentSeriesRing(K,prec);
_,y1:=find_fp(E1ext,u1,prec); 
if Coefficient(y1,0) ne Coefficient(v1,0) then y1:=-y1;end if;

S:=increase_precision_gluing(R1,R2,[u1+t,LSR!y1],m1,m2,HyperellipticPolynomials(H),prec);
phi1:=expression(S[1],S[2],[u1+t,LSR!y1],u1);



m1,m2:=Explode(constants_in_SDE_gluing(R3,R4,[u2+t,v2]));
_,y2:=find_fp(E2ext,u2,prec);
if Coefficient(y2,0) ne Coefficient(v2,0) then y2:=-y2;end if;

S:=increase_precision_gluing(R3,R4,[u2+t,LSR!y2],m1,m2,HyperellipticPolynomials(H),prec);
phi2:=expression(S[1],S[2],[u2+t,LSR!y2],u2);

temp1:=evaluate_phi(phi1,phi2,BaseChange(Jacobian(H),K),G[1]); 
temp2:=evaluate_phi(phi1,phi2,BaseChange(Jacobian(H),K),G[2]); 
if temp1 ne Parent(temp1)!0 or temp2 ne Parent(temp2)!0 then
phi2:=[phi2[1],phi2[2],-phi2[3],-phi2[4]];
end if;

return H, <phi1,phi2>;
end if;

end intrinsic;





/***********************(4) Splitting case ***************************************/
function orbit2(P,K)
    q:=#K;
    J:=Parent(P);
    R<x>:=Parent(P[1]);
    temp:=[];
    repeat
    Q:=J![&+[Coefficient(P[1],i)^q*x^i: i in [0..2]],&+[Coefficient(P[2],i)^q*x^i: i in [0,1]]];
    temp cat:=[Q];
    until Q eq P;
    return temp;
end function;

function representaion_of_kernel_g2(P1,P2,l,K)
    total:={i*P1+j*P2: i in [0..l-1], j in [0..l-1]};
    V:=[];
    while #total gt 0 do
    temp:=orbit2(Rep(total),K);
    V cat:=[<Rep(temp),#temp>];
    total:=total diff {i: i in temp};
    end while;
    m:=(l+1) div 2;

    return [<m*i[1], i[2]> : i in V];
end function;







function constants_for_curve(Jext,mu,kerV,K1,cij,l,fH)
   c01,c45,c12,c34,c23,c25:=Explode(cij);
   R<x>:=Parent((Jext!0)[1]);
   D24:=Jext![(x-mu[2])*(x-mu[4]),0];
   qq:=#K1;

   sum2:=invariant_section(kerV,Jext!0, D24,l,qq,fH);
   assert sum2 ne 0;
 
   sum1:=0;
   D01:=Jext![x-mu[1],0];
   sum1:=invariant_section(kerV, D01, D24,l,qq,fH);
   if sum1 eq 0 then
         D12:=Jext![(x-mu[1])*(x-mu[2]),0];
         temp:=invariant_section(kerV, D12, D24,l,qq,fH);
         h0010:=(c12*(mu[3]-mu[2])*(mu[5]-mu[2])*(mu[1]-mu[4]))^l*(temp/sum2)^2;

         D05:=Jext![x-mu[5],0];
         temp:=invariant_section(kerV, D05, D24,l,qq,fH); 
         c05:=c12*c34*(mu[3]-mu[1])*(mu[3]-mu[2])*(mu[4]-mu[1])*(mu[4]-mu[2]);
         h0011:=(c05*(mu[2]-mu[5])*(mu[4]-mu[5]))^l*(temp/sum2)^2;

        return true,[<[0,0,1,0],h0010>,<[0,0,1,1],h0011>], [1,0,0,0];
   else
        h1000:=(c01*(mu[2]-mu[1])*(mu[4]-mu[1]))^l*(sum1/sum2)^2;
   end if;

   D45:=Jext![(x-mu[4])*(x-mu[5]),0];
   sum1:=invariant_section(kerV, D45, D24,l,qq,fH);
   if sum1 eq 0 then
         D34:=Jext![(x-mu[3])*(x-mu[4]),0];
         temp:=invariant_section(kerV, D34, D24,l,qq,fH);
         h0001:=(c34*(mu[3]-mu[2])*(mu[4]-mu[1])*(mu[4]-mu[5]))^l*(temp/sum2)^2;
         D05:=Jext![x-mu[5],0];
         temp:=invariant_section(kerV, D05, D24,l,qq,fH); 
         c05:=c12*c34*(mu[3]-mu[1])*(mu[3]-mu[2])*(mu[4]-mu[1])*(mu[4]-mu[2]);
         h0011:=(c05*(mu[2]-mu[5])*(mu[4]-mu[5]))^l*(temp/sum2)^2;
        return true,[<[0,0,0,1],h0001>,<[0,0,1,1],h0011>], [0,1,0,0];
   else
        h0100:=(c45*(mu[4]-mu[1])*(mu[4]-mu[3])*(mu[5]-mu[2]))^l*(sum1/sum2)^2;
   end if;

 
   D12:=Jext![(x-mu[1])*(x-mu[2]),0];
   sum1:=invariant_section(kerV, D12, D24,l,qq,fH);
   if sum1 eq 0 then        
        D25:=Jext![(x-mu[5])*(x-mu[2]),0];
        temp:=invariant_section(kerV, D25, D24,l,qq,fH);
        c25:=c01*c34*(mu[3]-mu[1])*(mu[4]-mu[1]);
        h1001:=(c25*(mu[2]-mu[1])*(mu[3]-mu[2])*(mu[4]-mu[5]))^l*(temp/sum2)^2;
        return true,[<[1,0,0,0],h1000>,<[1,0,0,1],h1001>], [0,0,1,0];
   else
        h0010:=(c12*(mu[3]-mu[2])*(mu[5]-mu[2])*(mu[1]-mu[4]))^l*(sum1/sum2)^2;
   end if;


    D34:=Jext![(x-mu[3])*(x-mu[4]),0]; 
    sum1:=invariant_section(kerV, D34, D24,l,qq,fH);
    if sum1 eq 0 then
         D03:=Jext![x-mu[3],0];
         temp:=invariant_section(kerV, D03, D24,l,qq,fH);
         c03:=c45*c12*(mu[1]-mu[4])*(mu[1]-mu[5])*(mu[2]-mu[4])*(mu[2]-mu[5]);
         h0110:=(c03*(mu[2]-mu[3])*(mu[4]-mu[3]))^l*(sum1/sum2)^2;
        return true, [<[0,1,0,0],h0100>,<[0,1,1,0],h0110>], [0,0,0,1];
    else
        h0001:=(c34*(mu[3]-mu[2])*(mu[4]-mu[1])*(mu[4]-mu[5]))^l*(sum1/sum2)^2;
    end if;

    

    D23:=Jext![(x-mu[3])*(x-mu[2]),0];
    sum1:=invariant_section(kerV, D23, D24,l,qq,fH);
    if sum1 eq 0 then
        return true, [<[0,0,0,1],h0001>,<[0,0,1,0],h0010>], [1,1,0,0];
    else
        h1100:=(c23*(mu[2]-mu[1])*(mu[4]-mu[3])*(mu[5]-mu[2]))^l*(sum1/sum2)^2;
    end if;

    D25:=Jext![(x-mu[5])*(x-mu[2]),0];
    sum1:=invariant_section(kerV, D25, D24,l,qq,fH);
    if sum1 eq 0 then
         D05:=Jext![x-mu[5],0];
         temp:=invariant_section(kerV, D05, D24,l,qq,fH); 
         c05:=c12*c34*(mu[3]-mu[1])*(mu[3]-mu[2])*(mu[4]-mu[1])*(mu[4]-mu[2]);
         h0011:=(c05*(mu[2]-mu[5])*(mu[4]-mu[5]))^l*(temp/sum2)^2;
        return true,[<[0,0,1,0],h0010>,<[0,0,1,1],h0011>], [1,0,0,1];
    else
        c25:=c01*c34*(mu[3]-mu[1])*(mu[4]-mu[1]);
        h1001:=(c25*(mu[2]-mu[1])*(mu[3]-mu[2])*(mu[4]-mu[5]))^l*(sum1/sum2)^2;
    end if;
   
   
    mu3p:=h0100/(h1000*h1100);
    mu4p:=(h0001*h0100)/(h1001*h1100);
    mu5p:=h0001/(h1000*h1001);
   
    if #{0,1,mu3p,mu4p,mu5p} eq 5 then
            return false, [0,1,mu3p,mu4p,mu5p], [h1000,h0010];
    end if;

    D14:=Jext![(x-mu[1])*(x-mu[4]),0];
    sum1:=invariant_section(kerV, D14, D24,l,qq,fH);
    if sum1 eq 0 then
        return true, [<[1,0,0,0],h1000>,<[0,1,0,0],h0100>], [1,1,1,1];
    end if;

    D03:=Jext![x-mu[3],0];
    sum1:=invariant_section(kerV, D03, D24,l,qq,fH);       
    if sum1 eq 0 then
        D05:=Jext![x-mu[5],0];
        temp:=invariant_section(kerV, D05, D24,l,qq,fH); 
        c05:=c12*c34*(mu[3]-mu[1])*(mu[3]-mu[2])*(mu[4]-mu[1])*(mu[4]-mu[2]);
        h0011:=(c05*(mu[2]-mu[5])*(mu[4]-mu[5]))^l*(temp/sum2)^2;
        return true, [<[0,0,0,1],h0001>,<[0,0,1,1],h0011>], [0,1,1,0];
    else
       c03:=c45*c12*(mu[1]-mu[4])*(mu[1]-mu[5])*(mu[2]-mu[4])*(mu[2]-mu[5]);
       h0110:=(c03*(mu[2]-mu[3])*(mu[4]-mu[3]))^l*(sum1/sum2)^2;
       return true, [<[0,1,0,0], h0100>,<[0,1,1,0],h0110>], [0,0,1,1];
    end if;
   
end function;


/*
* s: a sequence of four elements from {0,1}.
* compute s[1]*D01+s[2]*D45+s[3]*D12+s[4]*D34
*/
function add_two_torsion(s)
    B:=[{0,1},{4,5},{1,2},{3,4}];
    S:={0,1,2,3,4,5};
    sum:={};
    for i in [1..4] do
    if s[i] eq 1 then
    sum:=sum sdiff B[i];
    end if;
    end for;
    if #sum gt 2 then
    sum:=S diff sum;
    end if;
    return sum;
end function;


function image_on_newcurve(lambda,x1,y1,Enew)
    R<x>:=PolynomialRing(Parent(lambda));
    E:=EllipticCurve(x*(x-1)*(x-lambda));
    _,f:=IsIsomorphic(E, BaseChange(Enew,Parent(lambda)));
    f:=DefiningPolynomials(f);
    temp:=[];

    for i in [1..3] do
    L1:=Coefficients(f[i]);
    L2:=[Exponents(j): j in Monomials(f[i])];
    temp cat:=[&+[L1[j]*x1^L2[j][1]*y1^L2[j][2]: j in [1..#L1]]];
    end for;
    return temp[1]/temp[3], temp[2]/temp[3];
end function; 

/*
* H: a genus 2 curve over K0
* l: an odd prime 
* P1,P2: generate a K0-rational isotropic subgroup of l-torsions w.r.t the Weil pairing
*/
intrinsic SplittingIsogeny(H::CrvHyp,P1::JacHypPt,P2::JacHypPt,l::RngIntElt: precomp:=AssociativeArray())->Tup
{}
   require Genus(H) eq 2: "The genus of Argument 1 is not 2";
   require  IsPrime(l) and IsOdd(l):    "Argument 4 is not an odd prime";
   require l*P1 eq Parent(P1)!0 and l*P2 eq Parent(P2)!0: "The order of Argument 2 or Argument 3 is not Argument 4";
   require WeilPairing(P1,P2,l) eq 1: "The Weil pairing of Argument 2 and Argument 3 is not trivial ";

   f,h:=HyperellipticPolynomials(H);
   require  Degree(f) eq 5 and h eq 0: "Argument 1 should be given by a univariate polynomial of degree 5";

   K0:=BaseRing(H);
   temp,K1:=RootsInSplittingField(f);
   mu:=[i[1]: i in temp];
   mu:=[mu[1],mu[2],mu[4],mu[3],mu[5]];
  // mu:=[mu[4],mu[3],mu[1],mu[2],mu[5]];
   vprint llisogeny: "The numbering of roots:\nmu=",mu,"\n"; 

   c01:=1/&*[mu[i]-mu[1]:i in [2..5]];
   c45:=1/&*[&*[mu[i]-mu[j]: j in [1,2,3]]: i in [4,5]];
   c12:=1/&*[&*[mu[i]-mu[j]:j in [3,4,5]]: i in [1,2]];
   c34:=1/&*[&*[mu[i]-mu[j]:j in [1,2,5]]: i in [3,4]];
   if &or[not IsSquare(i): i in [c01,c45,c12,c34]] then
       K1:=ext<K1|2>;
       mu:=[K1!i: i in mu];
   end if;
   
   c01:=Sqrt(K1!c01); c45:=Sqrt(K1!c45); c12:=Sqrt(K1!c12); c34:=Sqrt(K1!c34);
   c23:=c01*c45*(mu[4]-mu[1])*(mu[5]-mu[1]);
   c25:=c01*c34*(mu[4]-mu[1])*(mu[3]-mu[1]);
   
   J:=Jacobian(H);
   extdeg:=LCM([Degree(BaseRing(Curve(Parent(P1))),K0), Degree(BaseRing(Curve(Parent(P2))),K0), Degree(K1,K0)]);
   K2:=ext<K0|extdeg>; Embed(K1,K2); Embed(BaseRing(Curve(Parent(P1))),K2);
   Jext:=BaseChange(J,K2);
   kerV:=representaion_of_kernel_g2(Jext!P1,Jext!P2,l,K1);
   qq:=#K1;

 
  
   
  
   split,ab,char:=constants_for_curve(Jext,mu,kerV,K1,[c01,c45,c12,c34,c23,c25],l,f);
 
   if split then
        lambda1:=ab[1][2]^2; lambda2:=ab[2][2]^2;
        vprint llisogeny: "Legendre form y^2=x(x-1)(x-lambdai): lambda1=",lambda1, "lambda2=", lambda2, "char=", char, "\n";
        

        if lambda1 in K0 and lambda2 in K0 then
            P<x>:=PolynomialRing(K0);
            E3:=EllipticCurve(x*(x-1)*(x-lambda1)); E4:=EllipticCurve(x*(x-1)*(x-lambda2));
        else
            jE3:=2^8*(lambda1^2-lambda1+1)^3/(lambda1^2-lambda1)^2;
            jE4:=2^8*(lambda2^2-lambda2+1)^3/(lambda2^2-lambda2)^2;
            E3:=EllipticCurveFromjInvariant(K0!jE3); E3:=WeierstrassModel(E3);
            E4:=EllipticCurveFromjInvariant(K0!jE4); E4:=WeierstrassModel(E4); 
        end if;
        
        if not IsDefined(precomp, "LPolynomial") then 
          LP:=LPolynomial(H);
          else 
           LP:=precomp["LPolynomial"];
        end if;

        for i in Twists(E3), j in Twists(E4) do
            if LPolynomial(i)*LPolynomial(j) eq LP then
               E3new:=i; E4new:=j; 
               break i;
            end if;
        end for;
        
        if Characteristic(K0) lt (3*l+1) then
            printf "No implementation for the algebraic form of isogeny.\n";
            return <E3new,E4new>;
        end if;

       u,v:=find_fp(H,2,4);
       vprint llisogeny:"-- a formal point on the starting curve --\n","u=",u+Parent(v).1,"v=",v,"\n";
       
       j1,j2:=Explode(Sort([j: j in add_two_torsion(ab[1][1])]));
       j3,j4:=Explode(Sort([j: j in add_two_torsion(ab[2][1])]));

       RR:=PolynomialRing(Parent(v));  
       Dj12:=[&*[RR.1-mu[j]: j in [j1,j2]| j ne 0],0];
       Dj34:=[&*[RR.1-mu[j]: j in [j3,j4]| j ne 0],0];
       D24:=[(RR.1-mu[2])*(RR.1-mu[4]),0];

       sum1:=0; sum2:=0; sum3:=0;
       for S in kerV do
         temp:=[Coefficient(S[1][1],2)*RR.1^2+ Coefficient(S[1][1],1)*RR.1+Coefficient(S[1][1],0), Coefficient(S[1][2],1)*RR.1+Coefficient(S[1][2],0)];
         T1:=cantor_addition([RR.1-u-Parent(v).1,RR!v],temp,f,2);
         T2:=cantor_addition(T1,Dj12,f,2);
         T3:=cantor_addition(T1,Dj34,f,2);

         t1:=Parent(v)!double_and_add_g2(S[1],T1,D24,l,f);
         t2:=Parent(v)!double_and_add_g2(S[1],T2,D24,l,f);
         t3:=Parent(v)!double_and_add_g2(S[1],T3,D24,l,f);
         sum1+:=&+[trace(Coefficient(t1,tt),qq,S[2])*Parent(v).1^tt: tt in [0..2]];
         sum2+:=&+[trace(Coefficient(t2,tt),qq,S[2])*Parent(v).1^tt: tt in [0..2]];
         // printf "1615: t3=%o\n",t3;
         sum3+:=&+[trace(Coefficient(t3,tt),qq,S[2])*Parent(v).1^tt: tt in [0..2]];
       end for;

       /* [(u+t,v) - infty] sim  T1+T2- (mu2,0)-(mu4,0) */
       temp:=cantor_addition([RR.1-u-Parent(v).1,RR!v],D24,f,2);
       c03:=c45*c12*(mu[1]-mu[4])*(mu[1]-mu[5])*(mu[2]-mu[4])*(mu[2]-mu[5]);
       c05:=c12*c34*(mu[3]-mu[1])*(mu[3]-mu[2])*(mu[4]-mu[1])*(mu[4]-mu[2]);
       c25:=c01*c34*(mu[3]-mu[1])*(mu[4]-mu[1]);
       c02:=c01*c12*(mu[3]-mu[1])*(mu[4]-mu[1])*(mu[5]-mu[1]);
       case char:
           when [1,0,0,0]:
              A:=(c12*evaluate_eta(1,2,temp,mu))^l*(sum2/sum1)^2; B:=(c05*evaluate_eta(0,5,temp,mu))^l*(sum3/sum1)^2;
           when [0,1,0,0]: 
              A:=(c34*evaluate_eta(3,4,temp,mu))^l*(sum2/sum1)^2; B:=(c05*evaluate_eta(0,5,temp,mu))^l*(sum3/sum1)^2;
           when [0,0,1,0]:
              A:=(c01*evaluate_eta(0,1,temp,mu))^l*(sum2/sum1)^2; B:=(c25*evaluate_eta(2,5,temp,mu))^l*(sum3/sum1)^2;
           when [0,0,0,1]:
              A:=(c45*evaluate_eta(4,5,temp,mu))^l*(sum2/sum1)^2; B:=(c03*evaluate_eta(0,3,temp,mu))^l*(sum3/sum1)^2;
           when [1,1,0,0]:
              A:=(c34*evaluate_eta(3,4,temp,mu))^l*(sum2/sum1)^2; B:=(c12*evaluate_eta(1,2,temp,mu))^l*(sum3/sum1)^2;
           when [1,0,0,1]:
              A:=(c12*evaluate_eta(1,2,temp,mu))^l*(sum2/sum1)^2; B:=(c05*evaluate_eta(0,5,temp,mu))^l*(sum3/sum1)^2;
           when [0,1,1,0]:
              A:=(c34*evaluate_eta(3,4,temp,mu))^l*(sum2/sum1)^2; B:=(c05*evaluate_eta(0,5,temp,mu))^l*(sum3/sum1)^2;
           when [0,0,1,1]:
              A:=(c45*evaluate_eta(4,5,temp,mu))^l*(sum2/sum1)^2; B:=(c03*evaluate_eta(0,3,temp,mu))^l*(sum3/sum1)^2;
           when [1,1,1,1]:
              A:=(c01*evaluate_eta(0,1,temp,mu))^l*(sum2/sum1)^2; B:=(c45*evaluate_eta(4,5,temp,mu))^l*(sum3/sum1)^2;
       end case;
      
       x1:=ab[1][2]*(A*ab[1][2]-1)/(A-ab[1][2]);
       x2:=ab[2][2]*(B*ab[2][2]-1)/(B-ab[2][2]);
       
       y1:=Roots(RR.1^2-x1*(x1-1)*(x1-lambda1))[1][1];
       y2:=Roots(RR.1^2-x2*(x2-1)*(x2-lambda2))[1][1];
     
       x1,y1:=image_on_newcurve(lambda1,x1,y1,E3new);
       x2,y2:=image_on_newcurve(lambda2,x2,y2,E4new);

       vprint llisogeny: "-- (the) image of the chosen formal point -- ";
       vprint llisogeny: "x1=",x1, "y1=",y1;
       vprint llisogeny: "x2=",x2, "y2=",y2,"\n";
       prec:=3*l+1;
       u,v0:=find_fp(H,u,prec); 
       if Coefficient(v0,0) ne Coefficient(v,0) then v:=-v0; else v:=v0; end if;

       m1,m2:=Explode(constants_in_SDE_splitting([u+Parent(v).1,v],[x1,y1]));
       x1,y1:=Explode(increase_precision_splitting([x1,y1],[u+Parent(v).1,v],m1,m2,HyperellipticPolynomials(E3new),prec));
       
       m3,m4:=Explode(constants_in_SDE_splitting([u+Parent(v).1,v],[x2,y2]));
       x2,y2:=Explode(increase_precision_splitting([x2,y2],[u+Parent(v).1,v],m3,m4,HyperellipticPolynomials(E4new),prec));
       
       vprint llisogeny: "m1=", m1, "m2=", m2, "m3=", m3, "m4=", m4,"\n";
       U3:=rational_expr_reconstruct(x1,u);
       V3:=rational_expr_reconstruct(y1/v,u);
   
       U4:=rational_expr_reconstruct(x2,u);
       V4:=rational_expr_reconstruct(y2/v,u);
       // to do: determine the sign of V3 or V4
       return <E3new,[U3,V3],E4new,[U4,V4]>;

    else

        R<x>:=PolynomialRing(K1);
        H0:=HyperellipticCurve(&*[x-i: i in ab]);
        invariants:=IgusaInvariants(H0:normalize:=true);
        //H1:=HyperellipticCurveFromIgusaInvariants(invariants); 
        H1:=HyperellipticCurveFromIgusaClebsch(IgusaClebschInvariants(H0));
        H1:=is_isogenous(LP,K0,H1);

        if Characteristic(K0) lt (3*l/2+1) then
            printf "No implementation for the algebraic form of isogeny.\n";
            return <H1>;
        end if;

        u,v:=find_fp(H,0,3);

        RR:=PolynomialRing(Parent(v)); 
        sum0:=0; sum1:=0; sum2:=0; sum3:=0;
        D24:=[(RR.1-mu[2])*(RR.1-mu[4]),0];
        D01:=[RR.1-mu[1],0];
        D12:=[(RR.1-mu[1])*(RR.1-mu[2]),0];
        D02:=[RR.1-mu[2],0];

         for S in kerV do
         temp:=[Coefficient(S[1][1],2)*RR.1^2+ Coefficient(S[1][1],1)*RR.1+Coefficient(S[1][1],0), Coefficient(S[1][2],1)*RR.1+Coefficient(S[1][2],0)];
         T0:=cantor_addition([RR.1-u-Parent(v).1,RR!v],temp,f,2);
         temp:=double_and_add_g2(S[1],T0,D24,l,f);
         sum0+:=trace(temp,qq,S[2]);

         temp:=cantor_addition(T0,D01,f,2);
         temp:=double_and_add_g2(S[1],temp,D24,l,f);
         sum1+:=trace(temp,qq,S[2]);

         temp:=cantor_addition(T0,D12,f,2);
         temp:=double_and_add_g2(S[1],temp,D24,l,f);
         sum2+:=trace(temp,qq,S[2]);

         temp:=cantor_addition(T0,D02,f,2);
         temp:=double_and_add_g2(S[1],temp,D24,l,f);
         sum3+:=trace(temp,qq,S[2]);
       end for;
       temp:=cantor_addition([RR.1-u-Parent(v).1,RR!v],D24,f,2);
       sum0:=1/sum0;
       a1000:=(c01*evaluate_eta(0,1,temp,mu))^l*(sum1*sum0)^2;
       a0010:=(c12*evaluate_eta(1,2,temp,mu))^l*(sum2*sum0)^2;
       a1010:=(c02*evaluate_eta(0,2,temp,mu))^l*(sum3*sum0)^2;

        t1:=ab[4]/char[1];
        t2:=ab[4]*(ab[3]-1)*(ab[5]-1)/char[2];
        t3:=t2/(ab[3]*ab[5]*char[1]);
        x1x2:=t1*a1000;
        x1px2:=x1x2+1+t3*a1010;
        y1y2test:=t2*a0010;
        
        temp1,temp2:=find_root(y1y2test,[Coefficient(x1px2,i):i in [0,1,2]],[Coefficient(x1x2,i):i in [0,1,2]],ab);
        
        LSR<t>:=LaurentSeriesRing(K1,3);
        RRR<X>:=PolynomialRing(LSR);
        temp:=cantor_addition([(X-temp1[1])*(X-temp2[1]), X*(temp2[2]-temp1[2])/(temp2[1]-temp1[1])+(temp1[2]*temp2[1]-temp2[2]*temp1[1])/(temp2[1]-temp1[1])],
        [(X-1)*(X-ab[4]),0],X*(X-1)*(X-ab[3])*(X-ab[4])*(X-ab[5]),2);
        R1,R2:=Explode([[i[1],Evaluate(temp[2],i[1])]: i in Roots(temp[1])]);

        

        R1,R2:=Explode(image_under_isomorphism(H0,BaseChange(H1,K1),[R1,R2]));
        m1,m2,m3,m4:=Explode(constants_in_SDE_generic(R1,R2,[u+t,v]));

       prec:=Floor(3*l/2)+1;
       LSR<t>:=LaurentSeriesRing(K1,prec);
       vext:=find_fp(H,u,prec);
       if Coefficient(vext,0) ne Coefficient(v,0) then vext:=-vext;end if;

       S:=increase_precision_generic(R1,R2,[u+t,LSR!y1],m1,m2,m3,m4,HyperellipticPolynomials(H1),prec);
       phi:=expression(S[1],S[2],[u+t,LSR!y1],u);

       return <H1, phi>;

   end if;

end intrinsic;




/***********************(5) Example ***************************************/
function evalphi(phi1,phi2,J,P1P2)
  R<x>:=Parent((J!0)[1]);
  temp:=[Evaluate(i,P1P2[1][1]): i in phi1];
  first:=J![x^2-temp[1]*x+temp[2],(temp[3]*x+temp[4])*P1P2[1][2]];

  temp:=[Evaluate(i,P1P2[2][1]): i in phi2];
  second:=J![x^2-temp[1]*x+temp[2],(temp[3]*x+temp[4])*P1P2[2][2]];

  return first+second;
end function;




















