package finitefield;

import java.util.Arrays;
import java.lang.reflect.Array;
import java.math.BigInteger; 

public class PrincipalDavid {
	public static int p;
	public static int d;
	public static int n;
	public static int ell;
	public static int deg;
	public static boolean reci;
	public static int[] inv;
	public static int[] invq;
	public static int[] jac;
	public static int[] jacell;
	public static int N;
	public static int q;
	public static boolean ecf;
	public static boolean conj;
	
	public static int[] at= {1,0};
	public static int[] bt= {1,1};
	public static int[] unit = {1,1};
	
	public static int[] disc;
	
	public static int[][] addq;
	public static int[][] multq;
	
	public static void main(String args[])
    {
		long start = System.currentTimeMillis();
		
		///////////////////////////////////////////
		conj=true; //use conjecture to evaluate sign of func. eq.
		ecf=true; //with or without elliptic curve
		p=7; //base prime
		d=2; //degree of twists on F_p^n
		ell=3; //order of characters
		//////////////////////////////////////////
		q=p;
		n=1;
		
		while(q%ell!=1)
		{
			n++;
			q*=p;
			q=q%ell;
		}

		if(Math.pow(p, n)>=2147483647) 
		{
			System.out.println("Can't construct F_q");
			System.exit(0);
		}
		else
		{
			q=(int)Math.pow(p, n);
		}
		
		
		//deg of L-functions
		deg=2*n*d+3;
		N=(deg-1)/2;
		
		System.out.println("n="+n);
		inv = new int[p];
		invq = new int[q];
		jac = new int[p];
		jacell = new int[q];
		
		if(((p-1)/2)%2==1) reci=true;
		else reci=false;
		
		int i,j,k,l=0,v,z,tmp,tmp2,tmp3,tmp4,tmp5,tmp6,tmp7,pow,max,maxb;
		boolean f,g=true;
		
		int[] curve = new int[N+3];
		int[] pt = new int[N+3];
		long[][] coef = new long[deg+1][ell];
		long[][] coef2 = new long[deg+1][ell+1];
		int[] stat = new int[100];
		int nbcursed=0;
		long gcd;
		
		int irootstat=0;
		boolean iroot=true;
		boolean itmp;
		int maxrank=0;
		
		int mp=(int)Math.floor(n/2);
		max=((int)Math.pow(p, N+1)-1)/(p-1)-1;
		max*=2;
		max+=2771231;
		maxb=((int)Math.pow(p, mp+1)-1)/(p-1)-1;

		int nbdiffpoly=0;
		//long[][][] polydata = new long[max][2*N+1][ell];
		int[] polycount = new int[max];

		boolean dual=false;
		boolean conjtrue=true;
		if(p%3==2) dual=true;
		

		int[][] monic = new int[2][N]; //monic[0] list of primes, monic[1] (deg-1) of said prime
		int nbmon; //how many primes in monic minus one
		int[] poly = new int[N+2];
		int[] poly2 = new int[N+2];

		int[][] primelist = new int[N][max];
		int[] nbprime = new int[N]; //last index in primelist for prime of corresponding deg
		int[] am = new int[max];
		int[] triv = {2,0,1};
		
		boolean[] mlist = new boolean[max]; //to detect prime
		boolean[] twists = new boolean[max]; //squarefree and coprime to N_E (N_E=t)
		int[][] amcomp = new int[3][N+1];
		int amcompnb;
		boolean amflag;
		
		long btmp;

		long[] eqfsign = new long[ell];
		long[] eqfsign2 = new long[ell+1];
		long[] eqfsign3 = new long[ell+1];
		long[] eqfdenom = new long[ell];
		long[] eqftmp1 = new long[ell];
		long[] eqftmp2 = new long[ell];
		long[] eqftmp3 = new long[ell+1];
		long[] alpha = new long[ell+1];
		long[] alpha2 = new long[ell+1];
		long[] xne = new long[ell+1];
		long[] xsign=new long[ell+1];
		long[] monevec=new long[ell+1]; monevec[0]=-1;
		long denom;
		boolean alphaset = false;
		
		int[] jacmap = new int[q];
		boolean jm=true;
		boolean jmq=true;
		
		//int[] conductor= {3,0,0,1};
		//int[] conductor = {1,1};
		//int[] conductor = {3,0,p-1,1}; //legendre
		int[] conductor = {6,0,p-1,0,0,0,1};
		int[] testdiv;
		int m;
		
		int[] ext = new int[N];
		boolean extf=true;
		
		addq = new int[q][q];
		multq = new int[q][q];
		
		boolean amconstflag[] = new boolean[N+1];
		int amconst[] = new int[N+1];
		
		boolean lambda=false;
		boolean lambda2=false;

		int[] primefact = new int[max];
		int[][] family = new int[max][N+1];
		int fsize=0;

		int[][] pcomb = new int[N][N];
		int psize;
		
		int xidx=0;
		int xconj=0;
		
		int[] vcomb = new int[N];
		
		boolean tok;
		int jacret;
		
		boolean irrcond = true;
		int[] monefact = new int[2];
		int[] irrmone = {3,1,0,1};
		int idxmone = convert2(irrmone);
		int ifb;
		
		int deg2;
		
		if(p%4==1)
		{
			irrcond=false;
			tmp=0;
			for(i=1;i<p;i++)
			{
				if((i*i)%p==p-1)
				{
					monefact[tmp]=(((-1)*i)%p)+p;
					tmp++;
				}
			}
		}
		
		
		
		//computing inverses mod p
		for(i=1;i<p;i++)
		{
			inv[i]=slowexpo(i,p-2);
		}
		

		//jacobi symbol on F_p
		for(i=1;i<p;i++)
		{
			jac[i]=slowexpo(i,(p-1)/2);
			if(jac[i]==p-1) jac[i]=-1;
		}
		
		
		//prime of deg 1
		for(i=0;i<=p-1;i++)
		{
			primelist[0][i]=i;
			am[i]=ap(i);
			//testdiv=mod(disc,poly);
			
			if(!irrcond)
			{
				if(n*d==1 && i!=1 && i!=p-1 && i!=0 && i!=monefact[0] && i!=monefact[1])
				{
					family[fsize][0]=1;
					family[fsize][1]=i;
					fsize++;
				}
			}
			else
			{
				if(n*d==1 && i!=1 && i!=p-1 && i!=0)
				{
					family[fsize][0]=1;
					family[fsize][1]=i;
					fsize++;
				}
			}

			//prime powers
			poly=convert(i);
			poly2=Arrays.copyOf(poly,N+2);
			tmp=1;
			tmp3=i;
			for(j=1;j<N;j++)
			{
				poly2=mult(poly2,poly);
				tmp2=convert2(poly2);
				mlist[tmp2]=true;
				
				
				if(i==1) am[tmp2]=am[i]*am[tmp3]; //dealing with the bad primes
				else if(!irrcond && i==monefact[0]) am[tmp2]=am[i]*am[tmp3];
				else if(!irrcond && i==monefact[1]) am[tmp2]=am[i]*am[tmp3];
				else if(i==p-1) am[tmp2]=am[i]*am[tmp3];
				else if(i==0) am[tmp2]=am[i]*am[tmp3];
				else am[tmp2]=am[i]*am[tmp3]-p*tmp;
				
				
				tmp=am[tmp3];
				tmp3=tmp2;
			}
			
		}
		nbprime[0]=p-1;

		//computation of the a_M
		tmp2=p;
		pow=p*p;
		for(i=1;i<N;i++) //i+1 = deg of monics
		{
			System.out.println(i+"/"+(N-1));
			//fill with deg one primes (the first monic)
			for(j=0;j<=i;j++)
			{
				monic[0][j]=0;
				monic[1][j]=0;
			}
			nbmon=i;
			
			f=true;
			while(f)
			{
				//convert to its index
				tmp4=primelist[monic[1][0]][monic[0][0]];
				poly = convert(tmp4);
				amcompnb=1;
				amcomp[0][0]=tmp4;
				amcomp[1][0]=1;
				
				for(j=1;j<=nbmon;j++)
				{
					tmp4=primelist[monic[1][j]][monic[0][j]];
					poly=mult(poly,convert(tmp4));
					amflag=true;
					for(k=0;k<amcompnb;k++)
					{
						if(amcomp[0][k]==tmp4)
						{
							amcomp[1][k]++;
							amflag=false;
							k=amcompnb;
						}
					}
					if(amflag)
					{
						amcomp[0][amcompnb]=tmp4;
						amcomp[1][amcompnb]=1;
						amcompnb++;
					}
				}
				tmp4=convert2(poly);
				mlist[tmp4]=true;
				
				//compute a_M
				if(amcompnb>1)
				{
					if(i+1==n*d) amflag=true;
					else amflag=false;
					
					am[tmp4]=1;
					
					for(k=0;k<amcompnb;k++)
					{
						poly=convert(amcomp[0][k]);
						poly2=Arrays.copyOf(poly, N+2);
						for(l=1;l<amcomp[1][k];l++)
						{
							poly2=mult(poly2,poly);
						}
						am[tmp4]*=am[convert2(poly2)];
						if(amflag && (amcomp[0][k]==0 || amcomp[0][k]==1 || amcomp[0][k]==p-1 || (amcomp[0][k]==monefact[0] && !irrcond) || (amcomp[0][k]==monefact[1] && !irrcond) || (amcomp[0][k]==idxmone && irrcond) || (monic[1][k]+1)%n!=0)) amflag=false;
					}
					
					if(amflag && nbmon+1==amcompnb) //check if coprime to conductor and square-free
					{
						family[fsize][0]=amcompnb;
						for(k=0;k<amcompnb;k++)
						{
							family[fsize][k+1]=amcomp[0][k];
						}
						fsize++;
					}
					mlist[tmp4]=true;
				}
				
				
				//next monic
				if(monic[0][nbmon]!=nbprime[monic[1][nbmon]])
				{
					monic[0][nbmon]++;
				}
				else
				{
					tmp=monic[1][nbmon]+1;
					j=nbmon-1;
					
					while(j>0 && monic[0][j]==nbprime[monic[1][j]] && monic[1][j-1]==monic[1][j])
					{
						tmp+=monic[1][j]+1;
						j--;
					}

					if(j==0 && monic[1][0]==i-1 && monic[0][0]==nbprime[i-1])
					{
						f=false;
					}
					else
					{
						if(monic[0][j]==nbprime[monic[1][j]])
						{
							monic[0][j]=0;
							monic[1][j]++;
							tmp--;
							
							if(j!=0 && monic[1][j]==monic[1][j-1]) monic[0][j]=monic[0][j-1];
						}
						else
						{
							monic[0][j]++;
						}
						
						if(monic[1][j]==0) v=monic[0][j];
						else v=0;
						
						for(k=1;k<=tmp;k++)
						{
							monic[0][j+k]=v;
							monic[1][j+k]=0;
						}
						nbmon=j+tmp;
					}
				}
			}
			
			//unchecked are prime
			tmp3=tmp2+pow;
			pow*=p;
			v=(int)Math.pow(p,i+1);
			for(j=tmp2;j<tmp3;j++)
			{
				if(!mlist[j])
				{
					//a_P computation
					primelist[i][nbprime[i]]=j;
					am[j]=ap(j);

					//powers of P
					poly=convert(j);
					poly2=Arrays.copyOf(poly,N+2);

					if(i+1==d*n)
					{
						if(!(irrcond && j==idxmone)) //twists must be coprime to N_E
						{
							family[fsize][0]=1;
							family[fsize][1]=j;
							fsize++;
						}
					}

					if(i==n-1 && extf)
					{
						ext=Arrays.copyOf(poly,poly.length);
						extf=false;
					}
					tmp4=1;
					tmp6=j;
					for(k=1;k<(int)N/(i+1);k++)
					{
						poly2=mult(poly2,poly);
						tmp5=convert2(poly2);
						mlist[tmp5]=true;
						
						if(j==idxmone && irrcond) am[tmp5]=am[j]*am[tmp6];
						else am[tmp5]=am[j]*am[tmp6]-v*tmp4;
						
						tmp4=am[tmp6];
						tmp6=tmp5;
					}
					nbprime[i]++;
				}
			}

			tmp2=tmp3;
			nbprime[i]--;
		}
		
		System.out.println("Primes: OK");
		if(n==1) ext=triv;
		
		//constructing tables for F_q
		for(i=0;i<q;i++)
		{
			for(j=i;j<q;j++)
			{
				poly=cvt(i);
				poly2=cvt(j);
				tmp=cvt2(mod(add(poly,poly2),ext));
				addq[i][j]=tmp;
				addq[j][i]=tmp;
				tmp=cvt2(mod(mult(poly,poly2),ext));
				multq[i][j]=tmp;
				multq[j][i]=tmp;
			}
		}

		//computing inverses in F_q
		for(i=1;i<q;i++)
		{
			invq[i]=slowexpoq(i,q-2);
		}
				
				
		//jacobi order ell symbol on F_q
		for(i=1;i<q;i++)
		{
			tmp=slowexpoq(i,(q-1)/ell);
			if(tmp==1)
			{
				jacell[i]=0;
			}
			else if(jm)
			{
				jm=false;
				jacmap[tmp]=1;
				jacell[i]=1;
				for(j=2;j<=ell;j++) jacmap[slowexpoq(tmp,j)]=j;
						
			}
			else
			{
				jacell[i]=jacmap[tmp];
			}
		}
		
		System.out.println("F_q: OK");
		
		//factoring primes
		g=true;
		curve[0]=2;
		curve[2]=1;
		tmp2=2;
		
		while(g) {
			poly=Arrays.copyOf(curve, curve.length); //probably no need for this, poly=curve; poly2=curve; should work
			poly2=Arrays.copyOf(curve, curve.length);
			for(k=1;k<n;k++)
			{
				poly2=galois(poly2);
				poly=multq(poly,poly2);
			}

			tmp=convert2(poly);
			if(!mlist[tmp])
			{
				primefact[tmp]=convert2q(curve);
				mlist[tmp]=true;
			}
			
			j=1;
			while(curve[j]==q-1)
			{
				curve[j]=0;
				j++;
			}
			if(j==tmp2) 
			{
				if(j==d+1) g=false;
				else
				{
					curve[j]=0;
					curve[j+1]=1;
					curve[0]++;
					tmp2++;
				}
			}
			else curve[j]++;
		}
		
		
		System.out.println("Factoring: OK");
		
		//computation of factor at infinity of L(E,u)
		for(i=0;i<=deg;i++) for(j=0;j<=ell-1;j++) coef[i][j]=0;
		coef[0][0]=1;
		for(i=0;i<=N+1;i++) pt[i]=0;
			
		m=2;
			
		for(i=1;i<=m;i++) //no (1-u) factor
		{	
			pt[0]=i+1;
			pt[i+1]=1;
			for(j=1;j<i+1;j++) pt[j]=0;
			f=true;
					
			while(f)
			{
				coef[i][0]+=am[convert2(pt)];
				
				j=1;
				while(pt[j]==p-1)
				{
					pt[j]=0;
					j++;
				}
				if(j==i+1) f=false;
				else pt[j]++;
			}				
		}
		ifb=(int)coef[1][0]-p;
		if((int)coef[2][0]!=p*(1+ifb)) ifb=(int)coef[1][0]+p;
		if(ifb==(int)coef[1][0]-p && !irrcond) System.out.println("this shouldn't happen for ifb!!!");
		if(ifb!=(int)coef[1][0]-p && irrcond) System.out.println("this shouldn't happen for ifb!!!");
		
		//looping on the family
		for(z=0;z<fsize;z++)
		{
			//setting primes
			psize=family[z][0];
			for(i=1;i<=psize;i++)
			{
				pcomb[i-1]=convertq(primefact[family[z][i]]);
			}

			for(i=0;i<psize;i++) vcomb[i]=1;
			
			g=true;
			while(g)
			{
				//computation of zeta function of curve
				
				//check if char is even
				for(i=0;i<=N+1;i++) pt[i]=0;
				lambda2=true;
				if(xidx==0)
				{
					for(i=1;i<p;i++)
					{
						pt[0]=1;
						pt[1]=i;
						jacret=0;
						for(k=0;k<psize;k++)
						{
							tmp7=jacobiell(pt,pcomb[k]);
							tmp7*=vcomb[k];
							tmp7=tmp7%ell;
							jacret+=tmp7;
							jacret=jacret%ell;
						}
						if(jacret==1)
						{
							lambda2=false;
							xidx=i;
							xconj=1;
							i=p;
						}
					}
				}
				else
				{
					pt[0]=1;
					pt[1]=xidx;
					jacret=0;
					for(k=0;k<psize;k++)
					{
						tmp7=jacobiell(pt,pcomb[k]);
						tmp7*=vcomb[k];
						tmp7=tmp7%ell;
						jacret+=tmp7;
						jacret=jacret%ell;
					}
					if(jacret!=0)
					{
						xconj=jacret;
						lambda2=false;
					}
				}

				//initializing coefs of the frob poly
				for(i=0;i<=deg;i++) for(j=0;j<=ell-1;j++) { coef[i][j]=0; coef2[i][j]=0;}
				coef[0][0]=1;
				coef2[0][0]=1;
				for(i=0;i<=N+1;i++) pt[i]=0;
				
				if(lambda2) deg2=deg-2;
				else deg2=deg;
				
				if(deg2%2==0) m=deg2/2; //last coef to compute
				else m=(deg2-1)/2;
				
				//computation of first half of coefficients
				for(i=1;i<=m;i++) //no (1-u) factor
				{	
					pt[0]=i+1;
					pt[i+1]=1;
					for(j=1;j<i+1;j++) pt[j]=0;
					f=true;
						
					while(f)
					{
						if(ell==2)
						{
							coef[i][0]+=jacobi(pt,curve);
						}
						else 
						{
							tok=true;
							jacret=0;
							for(k=0;k<psize;k++)
							{
								tmp7=jacobiell(pt,pcomb[k]);
								if(tmp7==-1) tok=false;
								tmp7*=vcomb[k];
								tmp7=tmp7%ell;
								jacret+=tmp7;
								jacret=jacret%ell;
							}
								
							if(tok)
							{
								coef[i][jacret]+=am[convert2(pt)];
								if(i<=n*d-1) coef2[i][jacret]+=1;
							}
							//coef[i][0]+=am[convert2(pt)];
						}
						j=1;
							
						while(pt[j]==p-1)
						{
							pt[j]=0;
							j++;
						}
						if(j==i+1) f=false;
						else pt[j]++;
					}						
					//unique rep
					if(ell!=2) for(j=0;j<ell;j++) coef[i][j]-=coef[i][ell-1];
						
					//remove factor at infinity
					if (lambda2)
					{
						if(i==1)
						{
							coef[i][0]-=ifb;
						}
						else
						{
							for(j=0;j<ell;j++)
							{
								coef[i][j]-=ifb*coef[i-1][j];
								coef[i][j]-=p*coef[i-2][j];
							}
						}
					}
					//remove factor (1-u) from L(chi,u)
					if (lambda2 && i<=n*d-1) for(j=0;j<ell;j++) coef2[i][j]+=coef2[i-1][j];
				}

				//computing the sign of the func. eq.
				//additive reduction at inf
				
				/*
				//non-conjectural evaluation of sign of func eq.
				eqfsign=Arrays.copyOf(coef[m], coef[m].length);
				eqftmp1=Arrays.copyOf(coef[deg2-m], coef[deg2-m].length);
				eqfdenom=conjugate(eqftmp1,ell-1);
				
					eqfdenom=multcmplx(eqfdenom,eqftmp1);
					eqfsign=multcmplx(eqfsign,eqftmp1);
				
				denom=eqfdenom[0]-eqfdenom[ell-1];
				denom*=(long)Math.pow(p, 2*m-deg);

				for(j=0;j<ell;j++) eqfsign[j]-=eqfsign[ell-1];
				
				if(denom!=0)
				{
					gcd=gcd(denom,gcdarr(eqfsign));
					for(j=0;j<ell;j++)
					{
						eqfsign[j]/=gcd;
					}
					denom/=gcd;
					
					if(denom<0)
					{
						denom*=-1;
						for(j=0;j<ell;j++) eqfsign[j]*=-1;
					}
				}
				*/

				//computing chi(N_E)
				for(j=0;j<ell+1;j++) xne[j]=0;
				jacret=0;
				for(k=0;k<psize;k++)
				{
					tmp7=jacobiell(conductor,pcomb[k]);
			        tmp7*=vcomb[k];
					tmp7=tmp7%ell;
					jacret+=tmp7;
					jacret=jacret%ell;
				}
				
				xne[jacret]=1;
				
				//computing sign of f. e. of L(chi,u) squared
				if(n*d==1 || (lambda2 && n*d==2))
				{
					xsign[0]=1;
					for(j=1;j<=ell;j++) xsign[j]=0;
				}
				else
				{
					if(lambda2)
					{
						xsign=multcmplx2(coef2[n*d-2],coef2[n*d-2]);
						xsign[ell]=n*d-2;
					}
					else
					{
						xsign=multcmplx2(coef2[n*d-1],coef2[n*d-1]);
						xsign[ell]=n*d-1;
					}
				}
				
				if(!irrcond) xne=multcmplx2(xne,monevec); //multiplying by sign of f. e. of L(E,u)
				eqfsign2=multcmplx2(xne,xsign);
				
				eqfsign=Arrays.copyOf(eqfsign2, ell);
				denom=(long)Math.pow(p,eqfsign2[ell]);


				//System.out.println("/////////");
				/*
				if(!alphaset && !lambda2) //coded only for L-functions of even degree
				{
					if(denom==0)
					{
						System.out.println("bad luck!");
						System.exit(0);
					}
					eqfsign2=Arrays.copyOf(eqfsign, ell+1);
					eqfsign2[ell]=p_div(denom);
					reduce_cmplx(eqfsign2);
					alpha=divcmplx(eqfsign2,multcmplx2(xsign,xne));
					alphaset=true;
					System.out.print("alpha: ");
					displaylong(alpha);
				}
				
				if(lambda2)
				{
					alpha2[0]=1;
					for(j=1;j<=ell;j++) alpha2[j]=0;
				}
				else
				{
					alpha2=conjugate2(alpha,xconj);
				}
				
				for(k=0;k<=N+1;k++) pt[k]=0;
				pt[0]=1;
				pt[1]=2;
				jacret=0;
				for(k=0;k<psize;k++)
				{
					tmp7=jacobiell(pt,pcomb[k]);
					tmp7*=vcomb[k];
					tmp7=tmp7%ell;
					jacret+=tmp7;
					jacret=jacret%ell;
				}

				//conjectural evaluation
				
				eqfsign2=multcmplx2(multcmplx2(alpha2,xne),xsign);

				if(denom==0)
				{
					eqfsign=Arrays.copyOf(eqfsign2, ell);
					denom=(long)Math.pow(p,eqfsign2[ell]);
					nbcursed++;
				}
				else
				{
					eqfsign3=Arrays.copyOf(eqfsign, ell+1);
					eqfsign3[ell]=p_div(denom);
					reduce_cmplx(eqfsign3);
					if(!compare_cmplx(eqfsign2,eqfsign3))
					{
						conjtrue=false;
					}
				}
				*/
				//rest of coefficients
				btmp=(long)Math.pow(p, 2*(m+1)-deg2);
	
				for(j=m+1;j<=deg2;j++)
				{
					coef[j]=multcmplx(eqfsign,conjugate(coef[deg2-j],ell-1));
					for(i=0;i<ell-1;i++)
					{
						coef[j][i]-=coef[j][ell-1];
						coef[j][i]*=btmp;
						coef[j][i]/=denom;
					}
					coef[j][ell-1]=0;
					btmp*=p*p; //elliptic curve present
				}
				//displayzeta(coef);
				tmp=rankell(coef);
				//System.out.println("//////////  "+ z+"/"+fsize +"  ///////////");

				if(tmp>maxrank) maxrank=tmp;
				stat[tmp]++;
				itmp=isiaroot(coef);
				if(itmp!=ismiaroot(coef)) iroot=false;
						
						//distribution of zeta functions
						/*
						for(j=0;j<nbdiffpoly;j++)
						{
							for(k=0;k<=2*N;k++)
							{
								for(l=0;l<ell;l++)
								{
									if(coef[k][l]!=polydata[j][k][l])
									{
										k=2*N+2;
										l=ell+1;
									}
								}
							}
							
							if(k==2*N+1 && l==ell)
							{
								polycount[j]++;
								j=nbdiffpoly+1;
							}
						}
						
						if(j==nbdiffpoly)
						{
							polycount[j]++;
							nbdiffpoly++;
							
							for(k=0;k<=2*N;k++)
							{
								for(l=0;l<ell;l++)
								{
									polydata[j][k][l]=coef[k][l];
								}
							}
						}
						*/
						
						
				if(itmp) {irootstat++;}
					
				j=0;
				while(vcomb[j]==ell-1)
				{
					vcomb[j]=1;
					j++;
				}
				vcomb[j]++;
				if(j==psize-1) g=false;
			}
		}
		
		System.out.println("d="+(n*d));
		for(i=0;i<=maxrank;i++)
		{
			System.out.println("rank "+i+": "+stat[i]);
		}
		
		System.out.println("i root: " + irootstat);
		System.out.println("i root symmetry:"+iroot);
		long finish = System.currentTimeMillis();
		long timeElapsed = finish - start;
		
		
		//for(i=0;i<nbdiffpoly;i++)
		//{
			//for(j=0;j<=deg;j++) System.out.print(polydata[i][j][0]+",");
		//	System.out.println(":"+polycount[i]);
		//}
		//System.out.println("total:"+nbdiffpoly);
		System.out.println("cursed:"+nbcursed);
		System.out.println("conjecture:"+conjtrue);
		System.out.println("time:" + timeElapsed+"ms");
    }
	
	//deg b > deg a
	public static int jacobiell(int[] ai, int[] bi)
	{
		int ret=0;
		int tmp;
		
		int ad=ai.length;
		int bd=bi.length;
		
		if(ai[0]==-1) return -1;
		
		if(ai[0]==1)
		{
			if(ai[1]==0) return -1;
			return (jacell[ai[1]]*(bi[0]-1))%ell;
		}
		
		int[] a = Arrays.copyOf(ai, ad); 
		int[] b = Arrays.copyOf(bi, bd); 
		
		while(true)
		{
			ret+=jacell[a[a[0]]]*(b[0]-1);
			ret=ret%ell;
			
			tmp=jacell[b[b[0]]]*(a[0]-1);
			tmp=tmp%ell;
			tmp=(-1)*tmp+ell;
			
			ret+=tmp;
			ret=ret%ell;
			
			b=modq(b,a);
			
			if(b[0]==-1) return -1;
			
			if(b[0]==1)
			{
				if(b[1]==0) return -1;
				return (ret+(jacell[b[1]]*(a[0]-1)))%ell;
			}
			
			ret+=jacell[b[b[0]]]*(a[0]-1);
			ret=ret%ell;
			
			tmp=jacell[a[a[0]]]*(b[0]-1);
			tmp=tmp%ell;
			tmp=(-1)*tmp+ell;
			
			ret+=tmp;
			ret=ret%ell;
			
			a=modq(a,b);

			if(a[0]==-1) return -1;
			
			if(a[0]==1)
			{
				if(a[1]==0) return -1;
				return (ret+(jacell[a[1]]*(b[0]-1)))%ell;
			}
		}
	}
	
	public static int[] add(int[] ai, int[] bi)
	{
		int ret[];
		int al=ai[0];
		int bl=bi[0];
		int i;
		int op;
		
		if(al==bl)
		{
			op=(ai[al]+bi[al])%p;
			while(op==0 && al>1) {al--;op=(ai[al]+bi[al])%p;}
			ret = new int[al+1];
			for(i=1;i<al;i++) ret[i]=(ai[i]+bi[i])%p;
			ret[al]=op%p;
			ret[0]=al;
		}
		else if(al>bl)
		{
			ret = new int[al+1];
			for(i=1;i<=bl;i++) ret[i]=(ai[i]+bi[i])%p;
			for(i=bl+1;i<=al;i++) ret[i]=ai[i];
			ret[0]=al;
		}
		else
		{
			ret = new int[bl+1];
			for(i=1;i<=al;i++) ret[i]=(ai[i]+bi[i])%p;
			for(i=al+1;i<=bl;i++) ret[i]=bi[i];
			ret[0]=bl;
		}
		
		return ret;
	}
	
	
	public static int[] mult(int ai[], int[] bi)
	{
		int[] z= {1,0};
		if((ai[0]==1 && ai[1]==0)||(bi[0]==1 && bi[1]==0)) return z;
		
		int[] ret = new int[ai[0]+bi[0]];
		int i,j;
		
		for(i=1;i<=ai[0];i++)
		{
			for(j=1;j<=bi[0];j++)
			{
				ret[i+j-1]=(ret[i+j-1]+(ai[i]*bi[j]))%p;
			}
		}
		ret[0]=ai[0]+bi[0]-1;
		return ret;
	}
	
	public static int[] multq(int ai[], int[] bi)
	{
		int[] z= {1,0};
		if((ai[0]==1 && ai[1]==0)||(bi[0]==1 && bi[1]==0)) return z;
		
		int[] ret = new int[ai[0]+bi[0]];
		int i,j;
		
		for(i=1;i<=ai[0];i++)
		{
			for(j=1;j<=bi[0];j++)
			{
				ret[i+j-1]=addq[ret[i+j-1]][multq[ai[i]][bi[j]]];
			}
		}
		ret[0]=ai[0]+bi[0]-1;
		return ret;
	}
	
	public static int[] convert(int a)
	{
		int[] ret = new int[N+2];
		int i, k,j=2;
		int tmp=p;
		
		while(a>=tmp)
		{
			a-=tmp;
			tmp*=p;
			j++;
		}
		
		ret[0]=j;
		ret[j]=1;
		
		for(i=1;i<j;i++)
		{
			k=a%p;
			ret[i]=k;
			a-=k;
			a=a/p;
		}
		
		return ret;
	}
	
	public static long gcd(long a, long b)
	{
		long tmp;
		while(b!=0)
		{
			tmp=b;
			b=a%b;
			a=tmp;
		}
		
		return a;
	}
	
	public static long gcdarr(long[] a)
	{
		long ret=0;
		int i;
		for(i=0;i<a.length;i++)
		{
			ret=gcd(ret,a[i]);
		}
		return ret;
	}
	
	public static int convert2(int[] a)
	{
		int ret=0;
		int i;
		int ppow=1;
		int tmp=0;
		
		for(i=1;i<a[0];i++)
		{
			ret+=ppow*a[i];
			ppow*=p;
			tmp+=ppow;
		}
		tmp-=ppow;
		ret+=tmp;
		return ret;
	}
	
	public static int[] convertq(int a)
	{
		int[] ret = new int[N+2];
		int i, k,j=2;
		int tmp=q;
		
		while(a>=tmp)
		{
			a-=tmp;
			tmp*=q;
			j++;
		}
		
		ret[0]=j;
		ret[j]=1;
		
		for(i=1;i<j;i++)
		{
			k=a%q;
			ret[i]=k;
			a-=k;
			a=a/q;
		}
		
		return ret;
	}
	
	public static int convert2q(int[] a)
	{
		int ret=0;
		int i;
		int ppow=1;
		int tmp=0;
		
		for(i=1;i<a[0];i++)
		{
			ret+=ppow*a[i];
			ppow*=q;
			tmp+=ppow;
		}
		tmp-=ppow;
		ret+=tmp;
		return ret;
	}
	
	public static int[] mod(int[] ai, int[] bi)
	{
		int i;
		int temp;
		int mult;
		
		int[] a = Arrays.copyOf(ai, ai[0]+1); 
		int[] b = Arrays.copyOf(bi, bi[0]+1); 
		
		
		if(b[b[0]]<0) b[b[0]]+=p; //inverse doesnt deal with negative
		int c=inv[b[b[0]]];

		//put leading coef of b to -1
		for(i=1;i<b[0];i++)
		{
			b[i]=((b[i]*c)%p)*(-1);
		}
		
		while(true)
		{
			if(a[0]<b[0]) return a;
			
			mult=a[a[0]];

			a[a[0]]=0;
			temp=a[0]-1;

			for(i=b[0]-1;i>=1;i--)
			{
				a[temp]=(a[temp]+(b[i]*mult)%p)%p;				
				temp--;
			}
			
			for(i=a[0]-1;i>=1;i--)
			{
				if(a[i]!=0)
				{
					a[0]=i;
					if(a[i]<0) a[i]+=p;
					i=0;
				}
			}
			if(i==0) {a[0]=-1;return a;}
		}

	}
	
	public static int[] modq(int[] ai, int[] bi)
	{
		int i;
		int temp;
		int mult;
		
		int[] a = Arrays.copyOf(ai, ai[0]+1); 
		int[] b = Arrays.copyOf(bi, bi[0]+1); 
		
		int c=invq[b[b[0]]];

		//put leading coef of b to -1
		for(i=1;i<b[0];i++)
		{
			b[i]=multq[multq[b[i]][c]][p-1];
		}
		
		while(true)
		{
			if(a[0]<b[0]) return a;
			
			mult=a[a[0]];

			a[a[0]]=0;
			temp=a[0]-1;

			for(i=b[0]-1;i>=1;i--)
			{
				a[temp]=addq[a[temp]][multq[b[i]][mult]];
				temp--;
			}
			
			for(i=a[0]-1;i>=1;i--)
			{
				if(a[i]!=0)
				{
					a[0]=i;
					i=0;
				}
			}
			if(i==0) {a[0]=-1;return a;}
		}

	}
	
	public static boolean centralzero(long[] a)
	{
		boolean r=false;
		long cumul=0;
		for(int i=0;i<=2*d+1;i++)
		{
			cumul+=a[i]*(long)Math.pow(p, 2*d+1-i);
		}
		if(cumul==0) r=true;
		return r;
	}
	
	public static void dif(long[] a)
	{
		for(int i=0;i<2*d+1;i++)
		{
			a[i]=a[i+1]*(i+1);
		}
		a[2*d]=0;
	}
	
	public static int rank(long[] a)
	{
		int i;
		long[] b=Arrays.copyOf(a, a.length);
		
		for(i=0;i<=2*d+1;i++)
		{
			if(!centralzero(b)) return i;
			dif(b);
		}
		return i;
	}
	
	public static boolean centralzeroell(long[][] a)
	{
		boolean r=true;
		int i,j;
		long[][] cumul=new long[2][ell];
		
		//cumul[0][0]=(long)Math.pow(p, d-1);
		
		//for(i=1;i<=d-1;i++)
		for(i=0;i<=deg;i++)
		{
			for(j=0;j<ell;j++)
			{
				//no EC
				//cumul[1][j]+=a[2*i-1][j]*(long)Math.pow(p, d-1-i);
				//cumul[0][j]+=a[2*i][j]*(long)Math.pow(p, d-1-i);
				
				//with EC
				cumul[0][j]+=a[i][j]*(long)Math.pow(p, deg+2-i);
			}
		}
		for(j=0;j<ell;j++)
		{
			//if(cumul[0][j]!=0 || cumul[1][j]!=0) r=false;
			if(cumul[0][j]!=0) r=false;
		}
		return r;
	}
	
	public static boolean isiaroot(long[][] a)
	{
		boolean r=true;
		int i,j;
		long[][] cumul=new long[2][ell];
		
		cumul[0][0]=(long)Math.pow(p, d-1);
		
		for(i=1;i<=d-1;i++)
		{
			for(j=0;j<ell;j++)
			{
				if(i%2==1)
				{
					cumul[1][j]+=a[2*i-1][j]*(long)Math.pow(p, d-1-i);
					cumul[0][j]-=a[2*i][j]*(long)Math.pow(p, d-1-i);
				}
				else
				{
					cumul[1][j]-=a[2*i-1][j]*(long)Math.pow(p, d-1-i);
					cumul[0][j]+=a[2*i][j]*(long)Math.pow(p, d-1-i);
				}
			}
		}
		for(j=0;j<ell;j++)
		{
			if(cumul[0][j]!=0 || cumul[1][j]!=0) r=false;
		}
		return r;
	}
	
	public static boolean ismiaroot(long[][] a)
	{
		boolean r=true;
		int i,j;
		long[][] cumul=new long[2][ell];
		
		cumul[0][0]=(long)Math.pow(p, d-1);
		
		for(i=1;i<=d-1;i++)
		{
			for(j=0;j<ell;j++)
			{
				if(i%2==1)
				{
					cumul[1][j]-=a[2*i-1][j]*(long)Math.pow(p, d-1-i);
					cumul[0][j]-=a[2*i][j]*(long)Math.pow(p, d-1-i);
				}
				else
				{
					cumul[1][j]+=a[2*i-1][j]*(long)Math.pow(p, d-1-i);
					cumul[0][j]+=a[2*i][j]*(long)Math.pow(p, d-1-i);
				}
			}
		}
		for(j=0;j<ell;j++)
		{
			if(cumul[0][j]!=0 || cumul[1][j]!=0) r=false;
		}
		return r;
	}
	
	public static void difell(long[][] a)
	{
		int i,j;
		for(i=0;i<deg;i++)
		{
			for(j=0;j<ell;j++) a[i][j]=a[i+1][j]*(i+1);
		}

		for(j=0;j<ell;j++) a[deg][j]=0;
	}
	
	public static int rankell(long[][] a)
	{
		int i,j;
		long[][] b=new long[deg+1][ell];
		for(i=0;i<ell;i++)
		{
			for(j=0;j<deg+1;j++)
			{
				b[j][i]=a[j][i];
			}
		}
		
		for(i=0;i<=deg+1;i++)
		{
			if(!centralzeroell(b)) return i;
			difell(b);
		}
		return i;
	}
	
	
	public static int slowexpo(int a, int b)
	{
		int ret=1;
		int i;
		
		for(i=1;i<=b;i++)
		{
			ret=(ret*a)%p;
		}
		return ret;
	}
	
	public static int slowexpoq(int a, int b)
	{
		int ret=1;
		int i;
		
		for(i=1;i<=b;i++)
		{
			ret=multq[ret][a];
		}
		return ret;
	}
	
	public static int ap(int a)
	{
		int[] P = convert(a);
		int[] x = new int[P[0]];
		int[] x2;
		int i;
		int ret=0;
		boolean f=true;
		
		int[] mone = {1,p-1};
		int[] mt = {2,0,p-1};
		int[] pt = {2,0,1};
		int[] pts = {3,0,0,1};
		int[] mt2 = {3,0,0,p-1};
		int[] ac = {3,p-1,0,p-2};
		
		int debug=0;
		
		x[0]=1;

		while(f)
		{
			//x2=mult(x,x);
			//x2=mult(x2,x);
			//x2=add2(x2,mult2(at,x));
			//x2=add(x2,bt);

			//x2=mult(mult(x,add(x,mone)),add(x,mt)); //legendre
			x2=mult(mult(add(x,ac),add(x,mone)),add(x,mt2));
			
			ret+=jacobi(x2,P);
			i=1;
			x[1]=(x[1]+1)%p;
			while(f && x[i]==0)
			{
				i++;
				if(i==P[0])
				{
					f=false;
				}
				else
				{
					x[i]=(x[i]+1)%p;
					if(i>x[0]) x[0]++;
				}
			}
		}
		
		return (-1)*ret;
	}
	
	
	public static int jacobi(int[] ai, int[] bi)
	{
		int ret=1;
		
		if(ai[0]==-1) return 0;
		
		if(ai[0]==1)
		{
			if(jac[ai[1]]==-1 && bi[0]%2==0) ret*=-1;
			else if(ai[1]==0) return 0;
			return ret;
		}
		
		int[] a = Arrays.copyOf(ai, ai[0]+1); 
		int[] b = Arrays.copyOf(bi, bi[0]+1); 
		
		while(true)
		{
			if(jac[a[a[0]]]==-1 && b[0]%2==0) ret*=-1;
			if(jac[b[b[0]]]==-1 && a[0]%2==0) ret*=-1;
			if(reci && a[0]%2==0 && b[0]%2==0) ret*=-1;

			b=mod(b,a);

			if(b[0]==1)
			{
				if(jac[b[1]]==-1 && a[0]%2==0) ret*=-1;
				return ret;
			}
			else if(b[0]==-1)
			{
				return 0;
			}
			
			if(jac[a[a[0]]]==-1 && b[0]%2==0) ret*=-1;
			if(jac[b[b[0]]]==-1 && a[0]%2==0) ret*=-1;
			if(reci && a[0]%2==0 && b[0]%2==0) ret*=-1;
			
			a=mod(a,b);
			if(a[0]==1)
			{
				if(jac[a[1]]==-1 && b[0]%2==0) ret*=-1;
				return ret;
			}
			else if(a[0]==-1)
			{
				return 0;
			}
		}
	}
	
	public static long[] conjugate(long[] nb, int ord)
	{
		int i;
		long[] ret= new long[nb.length];
		
		ret[0]=nb[0];
		
		for(i=1;i<ell;i++)
		{
			ret[(ord*i)%ell]=nb[i];
		}
		
		return ret;
	}
	
	public static long[] conjugate2(long[] nb, int ord)
	{
		int i;
		long[] ret= new long[nb.length];
		
		ret[0]=nb[0];
		ret[ell]=nb[ell];
		
		for(i=1;i<ell;i++)
		{
			ret[(ord*i)%ell]=nb[i];
		}
		
		return ret;
	}
	
	
	public static long[] multcmplx(long[] a, long[] b)
	{
		long[] ret = new long[ell];
		int i,j;
		
		for(i=0;i<ell;i++) ret[i]=0;
		
		for(i=0;i<ell;i++)
		{
			for(j=0;j<ell;j++)
			{
				ret[(i+j)%ell]+=a[i]*b[j];
			}
		}
		
		return ret;
	}
	
	public static int p_div(long a)
	{
		int ret=0;
		if(a==0) return 100;
		while(a%p==0)
		{
			ret++;
			a=a/p;
		}
		
		return ret;
	}
	
    public static boolean compare_cmplx(long[] a, long[] b)
    {
    	int i;
 
    	for(i=0;i<=ell;i++)
    	{
    		if(a[i]!=b[i]) return false;
    	}
    	
    	return true;
    }
	
	public static void reduce_cmplx(long[] a) 
	{
		int min;
		int i,tmp;
		long div;

		for(i=0;i<=ell-1;i++) a[i]-=a[ell-1];
		
		min = p_div(a[0]);

		for(i=1;i<ell-1;i++)
		{
			tmp=p_div(a[i]);
			if(tmp<min) min=tmp; 
		}

		if(a[ell]<min) min=(int)a[ell];

		a[ell]-=(long)min;
		div=(long) Math.pow(p, min);

		for(i=0;i<ell-1;i++) a[i]=a[i]/div;
	}
	
	public static long[] multcmplx2(long[] a, long[] b)
	{
		long[] ret = new long[ell+1];
		int i,j;
		
		for(i=0;i<ell;i++)
		{
			for(j=0;j<ell;j++)
			{
				ret[(i+j)%ell]+=a[i]*b[j];
			}
		}

		ret[ell]=a[ell]+b[ell];
		reduce_cmplx(ret);
		return ret;
	}
	
	public static long[] divcmplx(long a[], long b[])
	{
		long[] acopy = Arrays.copyOf(a, a.length);
		long[] bcopy = Arrays.copyOf(b, b.length);
		long[] bcopy2 = Arrays.copyOf(b, b.length);
		acopy[ell]=0;
		bcopy[ell]=0;
		bcopy2[ell]=0;
		int pmult=(int)a[ell];
		int pdiv=(int)b[ell];
		int i;
		long denomp;
		int denomppow;
		long mult;
		long gcd;

		i=ell-1;
			acopy=multcmplx2(acopy,conjugate2(bcopy2,i));
			bcopy=multcmplx2(bcopy,conjugate2(bcopy2,i));
		
		denomp=bcopy[0]-bcopy[ell-1];

		for(i=0;i<ell;i++) acopy[i]-=acopy[ell-1];
		gcd=gcd(denomp,gcdarr(acopy));
		for(i=0;i<ell;i++) acopy[i]/=gcd;
		denomp/=gcd;
		
		if(denomp<0)
		{
			denomp*=-1;
			for(i=0;i<ell;i++) acopy[i]*=-1;
		}

		denomppow=p_div(denomp)+pmult-pdiv;
		if(denomppow<0)
		{
			mult=(long)Math.pow(p, (-1)*denomppow);
			for(i=0;i<ell;i++) acopy[i]*=mult;
		}
		else
		{
			acopy[ell]=denomppow;
		}

		reduce_cmplx(acopy);
		return acopy;
	}
	
	public static int[] discriminant()
	{
		int[] four = {1,4%p};
		int[] ts = {1,27%p};
		
		return add(mult(four,mult(mult(at,at),at)),mult(ts,mult(bt,bt)));
	}
	
	public static void display(int[] arr)
	{
		int i;
		for(i=0;i<arr.length-1;i++)
		{
			System.out.print(arr[i]+",");
		}
		System.out.println(arr[arr.length-1]);
	}
	
	public static void displaylong(long[] arr)
	{
		int i;
		for(i=0;i<arr.length-1;i++)
		{
			System.out.print(arr[i]+",");
		}
		System.out.println(arr[arr.length-1]);
	}
	/*
	public static int[] cvt(int i)
	{
		int[] ret = new int[3];
		
		ret[1]=i%p;
		i=i-ret[1];
		i=i/p;
		ret[2]=i;
		if(ret[2]==0) ret[0]=1;
		else ret[0]=2;
		return ret;
	}*/
	
	public static int[] cvt(int i)
	{
		int[] ret = new int[n+1];
		int j,k;
		
		for(j=1;j<n;j++)
		{
			ret[j]=i%p;
			i=i-ret[j];
			i=i/p;
		}
		ret[n]=i;
		
		for(j=n;j>1;j--)
		{
			if(ret[j]!=0)
			{
				ret[0]=j;
				return ret;
			}
		}
		ret[0]=1;
		return ret;
	}
	
	/*
	public static int cvt2(int[] i)
	{
		int ret=0;
		if(i[1]<0) i[1]+=p;
		ret+=i[1];
		if(i[0]>1)
		{
			if(i[2]<0) i[2]+=p;
			ret+=i[2]*p;
		}
		return ret;
	}*/
	
	public static int cvt2(int[] i)
	{
		int ret=0;
		int j;
		int pow=1;

		for(j=1;j<=i[0];j++) if(i[j]<0) i[j]+=p;
		
		for(j=1;j<=i[0];j++)
		{
			ret+=i[j]*pow;
			pow*=p;
		}
		
		return ret;
	}
	
	public static int[] galois(int[] a)
	{
		int[] ret=new int[a[0]+1];
		int i;
		
		for(i=1;i<=a[0];i++)
		{
			ret[i]=slowexpoq(a[i],p);
		}
		
		ret[0]=a[0];
		return ret;
	}
	
	public static void displayzeta(long[][] a)
	{
		int i,j;
		
		for(i=0;i<=deg;i++)
		{
			for(j=0;j<ell-1;j++)
			{
				System.out.print(a[i][j]+",");
			}
			System.out.print(a[i][j]);
			System.out.println("");
		}
		System.out.println("");
	}
	
	public static void displaycurve(int[] a)
	{
		int i;
		
		for(i=0;i<a.length;i++) System.out.print(a[i]+",");
		System.out.println("");
	}
}