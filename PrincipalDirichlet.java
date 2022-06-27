package finitefield;

import java.util.Arrays;
import java.lang.reflect.Array;
import java.math.BigInteger; 

public class PrincipalDirichlet {
	public static int p;
	public static int d;
	public static int n;
	public static int ell;
	public static int deg;
	public static boolean reci;
	public static boolean thin;
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
		///////////////////////////////////////////
		conj=true; //use conjecture to evaluate sign of func. eq.
		ecf=true; //with or without elliptic curve
		thin=true; //thin family: no exponents on character factors
		p=23; //base prime
		d=2; //degree of twists on F_p^n
		ell=11; //order of characters
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
		
		
		//deg of L-functions (without (1-u) factor)
		deg=n*d-1;
		N=n*d;
		
		System.out.println("n="+n);

		inv = new int[p];
		invq = new int[q];
		jac = new int[p];
		jacell = new int[q];
		
		if(((p-1)/2)%2==1) reci=true;
		else reci=false;
		
		int i,j,k,l=0,v,z,tmp,tmp2,tmp3,tmp4,tmp5,tmp6,tmp7,pow,max,maxb;
		boolean f,g=true;
		
		int[] curve = new int[N+2];
		int[] pt = new int[N+2];
		long[][] coef = new long[deg+2][ell];
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
		max+=77711455;
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
		int[] poly3 = new int[N+2];
		int[] poly4 = new int[N+2];
		int[] poly5 = new int[N+2];

		int[][] primelist = new int[N][max];
		int[] nbprime = new int[N]; //last index in primelist for prime of corresponding deg
		int[] am = new int[max];
		int[] triv = {2,0,1};
		
		boolean[] mlist = new boolean[max]; //to detect prime
		boolean[] twists = new boolean[max]; //squarefree and coprime to N_E (N_E=t)
		int[][] amcomp = new int[3][N+1];
		int amcompnb;
		boolean amflag;
		int deg2;
		
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
		long denom;
		boolean alphaset = false;
		
		int[] jacmap = new int[q];
		boolean jm=true;
		boolean jmq=true;
		boolean c;
		
		//int[] conductor= {3,0,0,1};
		//int[] conductor = {1,1};
		int[] conductor = {3,0,p-1,1}; //legendre
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
		
		boolean atrack[] = new boolean[10000];
		
		
		long start = System.currentTimeMillis();
		
		BigInteger[] eqfsignb = new BigInteger[ell];
		BigInteger[] eqftmp1b = new BigInteger[ell];
		BigInteger[] eqftmp2b = new BigInteger[ell];
		BigInteger[] eqfdenomb = new BigInteger[ell];
		BigInteger denomb;
		BigInteger gcdb;
		
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
			//am[i]=ap(i);
			//testdiv=mod(disc,poly);
			
			if(n*d==1)
			{
				family[fsize][0]=1;
				family[fsize][1]=i;
				fsize++;
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
				
				//if(i==0) am[tmp2]=am[i]*am[tmp3]; //dealing with the bad primes
				//else if(i==p-1) am[tmp2]=am[i]*am[tmp3];
				//else am[tmp2]=am[i]*am[tmp3]-p*tmp;
				
				
				//tmp=am[tmp3];
				//tmp3=tmp2;
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
					
					//am[tmp4]=1;
					
					for(k=0;k<amcompnb;k++)
					{
						poly=convert(amcomp[0][k]);
						poly2=Arrays.copyOf(poly, N+2);
						for(l=1;l<amcomp[1][k];l++)
						{
							poly2=mult(poly2,poly);
						}
						//am[tmp4]*=am[convert2(poly2)];
						//if(amflag && amcomp[1][k]!=1) amflag=false; 
						if(amflag && (monic[1][k]+1)%n!=0) amflag=false;
					}
					
					if(amflag && nbmon+1==amcompnb) 
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
					//am[j]=ap(j);

					//powers of P
					poly=convert(j);
					poly2=Arrays.copyOf(poly,N+2);
					
					if(i+1==d*n)
					{
						family[fsize][0]=1;
						family[fsize][1]=j;
						fsize++;
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
						//am[tmp5]=am[j]*am[tmp6]-v*tmp4;
						
						//tmp4=am[tmp6];
						//tmp6=tmp5;
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
				//initializing coefs of the frob poly
				for(i=0;i<=deg;i++) for(j=0;j<=ell-1;j++) { coef[i][j]=0;}
				coef[0][0]=1;
				for(i=0;i<=N+1;i++) pt[i]=0;
				
				//check if char is even
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

				if(lambda2) deg2=deg-1;
				else deg2=deg;
				
				if(deg2%2==0) m=deg2/2; //last coef to compute
				else m=(deg2+1)/2;

				for(i=0;i<=N+1;i++) pt[i]=0;
				
				//m=deg2;
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
								coef[i][jacret]+=1;
							}
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
						
					//remove factor 1-u
					if (lambda2) for(j=0;j<ell;j++) coef[i][j]+=coef[i-1][j];
					
					//need a non-zero coef
					if(i==m)
					{
						j=0;
						while(j<ell && coef[i][j]==0) j++;
						if(j==ell) m++; //need to compute another coef (for sign of func. eq.)
					}
				}
				
				
				//computing the sign of the func. eq.
				for(j=0;j<ell;j++) eqfsignb[j]=BigInteger.valueOf(coef[m][j]);
				for(j=0;j<ell;j++) eqftmp1b[j]=BigInteger.valueOf(coef[deg2-m][j]);
				eqfdenomb=conjugateb(eqftmp1b,ell-1);
				
				for(j=1;j<ell-1;j++)
				{
					eqftmp2b=conjugateb(eqftmp1b,j);
					eqfdenomb=multcmplxb(eqfdenomb,eqftmp2b);
					eqfsignb=multcmplxb(eqfsignb,eqftmp2b);
				}
				denomb=eqfdenomb[0].subtract(eqfdenomb[ell-1]);
				
				for(j=0;j<ell;j++) eqfsignb[j]=eqfsignb[j].subtract(eqfsignb[ell-1]);
				
				if(!denomb.equals(BigInteger.valueOf(0)))
				{
					gcdb=denomb.gcd(gcdarrb(eqfsignb));
					for(j=0;j<ell;j++)
					{
						eqfsignb[j]=eqfsignb[j].divide(gcdb);
					}
					denomb=denomb.divide(gcdb);
					
					if(denomb.compareTo(BigInteger.valueOf(0))==-1)
					{
						denomb=denomb.multiply(BigInteger.valueOf(-1));
						for(j=0;j<ell;j++) eqfsignb[j]=eqfsignb[j].multiply(BigInteger.valueOf(-1));
					}
				}
				
				for(j=0;j<ell;j++) eqfsign[j]=eqfsignb[j].longValue();
				denom=denomb.longValue();

					
				//rest of coefficients
				btmp=(long)p;
	
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
					btmp*=p; 
				}
				
				
				 
				//finding E_0s
				c=true;
				
				for(j=1;j<=deg2;j++)
				{
					for(i=1;i<ell;i++) if(coef[j][i]!=0) c=false;
				}
				if(coef[deg2][0]!=p) c=false;
				if(c && !atrack[(int)coef[1][0]+1000]) {
					atrack[(int)coef[1][0]+1000]=true;
					displayzeta(coef);
					System.out.println("-------------");
					for(k=0;k<psize;k++)
					{
						poly=Arrays.copyOf(pcomb[k], pcomb[k].length);
						poly2=Arrays.copyOf(pcomb[k], pcomb[k].length);
						for(l=1;l<n;l++)
						{
							poly2=galois(poly2);
							poly=multq(poly,poly2);
						}
						
						displaycurve(poly);
						System.out.println(vcomb[k]);
					}
					System.out.println("/////////////////////////////");
				}
				
				//displayzeta(coef);
				//System.out.println("/////////////////////////////");
				tmp=rankell(coef);

				if(tmp>maxrank) maxrank=tmp;
				stat[tmp]++;
				itmp=isiaroot(coef);
				if(itmp!=ismiaroot(coef)) iroot=false;
				/*
				if(itmp && vcomb[0]==1) //order 5 only 
				{
					System.out.println(vcomb[1]);
					for(k=0;k<poly3.length;k++) poly3[k]=0;
					poly3[0]=1;
					poly3[1]=5%p;
					for(k=0;k<poly4.length;k++) poly4[k]=0;
					poly4[0]=1;
					poly4[1]=p-1;
					
					
					poly=multq(pcomb[0],pcomb[1]);
					poly2=galois(poly);
					
					displaycurve(multq(multq(multq(poly,poly2),poly3),poly4));
					
					displaycurve(multq(powq(multq(poly,poly2),2),poly3));
					displaycurve(multq(addq(multq(poly,powq(poly2,4)),multq(poly2,powq(poly,4))),poly4));
					System.exit(0);
				}*/ 
				
						
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
				if(j==psize-1 || thin) g=false;
			}
		}
		System.out.println("d="+(n*d));
		for(i=0;i<=maxrank;i++)
		{
			System.out.println("rank "+i+": "+stat[i]);
		}
		
		System.out.println("i root: " + irootstat);
		if(!iroot) System.out.println("!!!i ROOT SYMMETRY FALSE!!!");
		long finish = System.currentTimeMillis();
		long timeElapsed = finish - start;
		
		
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
	
	public static int[] addq(int[] ai, int[] bi)
	{
		int ret[];
		int al=ai[0];
		int bl=bi[0];
		int i;
		int op;
		
		if(al==bl)
		{
			op=addq[ai[al]][bi[al]];
			while(op==0 && al>1) {al--;op=addq[ai[al]][bi[al]];}
			ret = new int[al+1];
			for(i=1;i<al;i++) ret[i]=addq[ai[i]][bi[i]];
			ret[al]=op;
			ret[0]=al;
		}
		else if(al>bl)
		{
			ret = new int[al+1];
			for(i=1;i<=bl;i++) ret[i]=addq[ai[i]][bi[i]];
			for(i=bl+1;i<=al;i++) ret[i]=ai[i];
			ret[0]=al;
		}
		else
		{
			ret = new int[bl+1];
			for(i=1;i<=al;i++) ret[i]=addq[ai[i]][bi[i]];
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
	
	public static int[] powq(int ai[], int pow)
	{
		int i;
		int[] ret = Arrays.copyOf(ai, ai.length);
		
		for(i=1;i<pow;i++)
		{
			ret=multq(ret,ai);
		}
		
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
	

	public static BigInteger gcdarrb(BigInteger[] a)
	{
		BigInteger ret=BigInteger.valueOf(0);
		int i;
		for(i=0;i<a.length;i++)
		{
			ret=ret.gcd(a[i]);
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
		int ppow=(int)Math.floor(deg/2);
		
		for(i=0;i<=deg;i++)
		{
			for(j=0;j<ell;j++)
			{
				//no EC
				cumul[i%2][j]+=a[i][j]*(long)Math.pow(p, ppow);
				//with EC
				//cumul[0][j]+=a[i][j]*(long)Math.pow(p, deg+2-i);
			}
			if(i%2==1) ppow--;
		}
		for(j=0;j<ell;j++)
		{
			if(cumul[0][j]!=0 || cumul[1][j]!=0) r=false;
			//if(cumul[0][j]!=0) r=false;
		}
		return r;
	}
	
	public static boolean isiaroot(long[][] a)
	{
		boolean r=true;
		int i,j;
		long[][] cumul=new long[2][ell];
		int ppow=(int)Math.floor(deg/2);
		
		for(i=0;i<=deg;i++)
		{
			for(j=0;j<ell;j++)
			{
				//no EC
				if(i%4==0 || i%4==1) cumul[i%2][j]+=a[i][j]*(long)Math.pow(p, ppow);
				else cumul[i%2][j]-=a[i][j]*(long)Math.pow(p, ppow);
				//with EC
				//cumul[0][j]+=a[i][j]*(long)Math.pow(p, deg+2-i);
			}
			if(i%2==1) ppow--;
		}
		for(j=0;j<ell;j++)
		{
			if(cumul[0][j]!=0 || cumul[1][j]!=0) r=false;
			//if(cumul[0][j]!=0) r=false;
		}
		return r;
	}
	
	public static boolean ismiaroot(long[][] a)
	{
		boolean r=true;
		int i,j;
		long[][] cumul=new long[2][ell];
		int ppow=(int)Math.floor(deg/2);
		
		for(i=0;i<=deg;i++)
		{
			for(j=0;j<ell;j++)
			{
				//no EC
				if(i%4==0 || i%4==3) cumul[i%2][j]+=a[i][j]*(long)Math.pow(p, ppow);
				else cumul[i%2][j]-=a[i][j]*(long)Math.pow(p, ppow);
				//with EC
				//cumul[0][j]+=a[i][j]*(long)Math.pow(p, deg+2-i);
			}
			if(i%2==1) ppow--;
		}
		for(j=0;j<ell;j++)
		{
			if(cumul[0][j]!=0 || cumul[1][j]!=0) r=false;
			//if(cumul[0][j]!=0) r=false;
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
		long[][] b=new long[deg+2][ell];
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
		
		int debug=0;
		
		x[0]=1;

		while(f)
		{
			//x2=mult(x,x);
			//x2=mult(x2,x);
			//x2=add2(x2,mult2(at,x));
			//x2=add(x2,bt);

			x2=mult(mult(x,add(x,mone)),add(x,mt)); //legendre
			
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
	
	
	public static BigInteger[] conjugateb(BigInteger[] nb, int ord)
	{
		int i;
		BigInteger[] ret= new BigInteger[nb.length];
		
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
	
	public static BigInteger[] conjugate2b(BigInteger[] nb, int ord)
	{
		int i;
		BigInteger[] ret= new BigInteger[nb.length];
		
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
	
	public static BigInteger[] multcmplxb(BigInteger[] a, BigInteger[] b)
	{
		BigInteger[] ret = new BigInteger[ell];
		int i,j;
		
		for(i=0;i<ell;i++) ret[i]=BigInteger.valueOf(0);
		
		for(i=0;i<ell;i++)
		{
			for(j=0;j<ell;j++)
			{
				ret[(i+j)%ell]=ret[(i+j)%ell].add(a[i].multiply(b[j]));
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
	
	public static int p_divb(BigInteger a)
	{
		int ret=0;
		if(a.equals(BigInteger.valueOf(0))) return 100;
		while(a.mod(BigInteger.valueOf(p)).equals(BigInteger.valueOf(0)))
		{
			ret++;
			a=a.divide(BigInteger.valueOf(p));
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
	
	public static void test(BigInteger[] a)
	{
		a[0]=a[0].add(a[0]);
	}
	
	public static void reduce_cmplxb(BigInteger[] a) 
	{
		int min;
		int i,tmp;
		BigInteger div;

		for(i=0;i<=ell-1;i++) a[i]=a[i].subtract(a[ell-1]);
		
		min = p_divb(a[0]);

		for(i=1;i<ell-1;i++)
		{
			tmp=p_divb(a[i]);
			if(tmp<min) min=tmp; 
		}

		if(a[ell].intValue()<min) min=a[ell].intValue();

		a[ell]=a[ell].subtract(BigInteger.valueOf(min));
		div=BigInteger.valueOf(p).pow(min);

		for(i=0;i<ell-1;i++) a[i]=a[i].divide(div);
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
	
	public static BigInteger[] multcmplx2b(BigInteger[] a, BigInteger[] b)
	{
		int i,j;
		BigInteger[] ret = new BigInteger[ell+1];
		for(i=0;i<=ell;i++) ret[i]=BigInteger.ZERO;
		for(i=0;i<ell;i++)
		{
			for(j=0;j<ell;j++)
			{
				ret[(i+j)%ell]=ret[(i+j)%ell].add(a[i].multiply(b[j]));
			}
		}

		ret[ell]=a[ell].add(b[ell]);
		reduce_cmplxb(ret);
		return ret;
	}
	
	public static long[] divcmplx(long a[], long b[])
	{
		int al=a.length;
		int bl=b.length;
		int i;
		long[] acopy = new long[al];
		BigInteger[] acopyb = new BigInteger[al];
		BigInteger[] bcopyb = new BigInteger[bl];
		BigInteger[] bcopy2b = new BigInteger[bl];
		
		int pmult=(int)a[ell];
		int pdiv=(int)b[ell];
		BigInteger denompb;
		long denomp;
		int denomppow;
		long mult;
		BigInteger gcd;

		for(i=0;i<al;i++) acopyb[i]=BigInteger.valueOf(a[i]);
		for(i=0;i<al;i++) bcopyb[i]=BigInteger.valueOf(b[i]);
		for(i=0;i<al;i++) bcopy2b[i]=BigInteger.valueOf(b[i]);
		
		acopyb[ell]=BigInteger.valueOf(0);
		bcopyb[ell]=BigInteger.valueOf(0);
		bcopy2b[ell]=BigInteger.valueOf(0);
		
		for(i=2;i<ell;i++)
		{
			acopyb=multcmplx2b(acopyb,conjugate2b(bcopy2b,i));
			bcopyb=multcmplx2b(bcopyb,conjugate2b(bcopy2b,i));
		}
		denompb=bcopyb[0].subtract(bcopyb[ell-1]);

		for(i=0;i<ell;i++) acopyb[i]=acopyb[i].subtract(acopyb[ell-1]);
		gcd=denompb.gcd(gcdarrb(acopyb));
		for(i=0;i<ell;i++) acopyb[i]=acopyb[i].divide(gcd);
		denompb=denompb.divide(gcd);
		
		for(i=0;i<al;i++) acopy[i]=acopyb[i].longValue();
		denomp=denompb.longValue();
		
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
	}
	
	public static void displaycurve(int[] a)
	{
		int i;
		
		for(i=0;i<a.length;i++) System.out.print(a[i]+",");
		System.out.println("");
	}
}