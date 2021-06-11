// Lattice gas code in 2d.
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <mygraph.h>
#include <time.h>
#include <gsl/gsl_rng.h>
#include <gsl/gsl_randist.h>
//Define System Dimension and Velocities 
#define xdim 32
#define ydim 32
#define V 9      //number of velocities, vx=v%3-1 vy=v/3-1
#define VPlus 10

//Define Variables
int iterations=0, XDIM=xdim, YDIM=ydim;
double Nav=10;
int C=100;
double N[xdim][ydim],NU[xdim][ydim][2],nn[V][xdim][ydim];
int Nreq=0,NUreq=0,nnreq=0;
int n[V][xdim][ydim];
double Tau=1.;
int NILeft[V];

int PMAX = 200;
int streamdebug=0;

const gsl_rng_type * TYPE;
gsl_rng * RANDOM;

int sample=0, lookup=0, gsl=0, FivePoint=0, SevenPoint=0, collision=0, multinomial=0;

double w[V]={1./36,1./9,1./36,1./9,4./9,1./9,1./36,1./9,1./36};
double pp[V]; // relative cummulative probability

double nav[xdim],nav_th[xdim];
int nav_req=0, nav_th_req=0;
//Define Structures
typedef struct {
  int bhalf, bquarter, b3quarter;
  double Sumhalf,LBhalf, Sumquarter, LBquarter, Sum3quarter, LB3quarter;
} BinArray_t;
BinArray_t *Lookup[VPlus]={NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL};
// You need one array for each w[i] size, i.e. 9 for D2Q9, with one extra added to allow for sampling Tau

typedef struct {
  int b50, b70, b85, b30, b15;
  double Sum50, Sum70, Sum85, Sum30, Sum15,LB50, LB70, LB85, LB30, LB15;
} BinArray_5t;
BinArray_5t *Lookup5Pt[VPlus]={NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL};

typedef struct {
  int b50, b70, b80, b90, b30, b20, b10;
  double Sum50, Sum70, Sum80, Sum90, Sum30, Sum20, Sum10, LB50, LB70, LB80, LB90, LB10, LB20, LB30;
} BinArray_7t;
BinArray_7t *Lookup7Pt[VPlus]={NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL};

int poisson(double lam){
  double r = (double) rand()/RAND_MAX;
  double Pois = exp(-lam);
  int p=0;
  double Sum= Pois;
  while (r>=Sum){
    p++;
    Pois*=lam/p;
    Sum+= Pois;
  }
  return p;
}

int poissonLog(double lam){
  double r = (double) rand()/RAND_MAX;
  double LPois = -lam;
  int p=0;
  double Sum= exp(LPois);
  while (r>=Sum){
    p++;
    LPois+=log(lam/p);
    Sum+= exp(LPois);
  }
  return p;
}

int binomial(int N,double p){
  double q=1-p;
  double r = (double) rand()/RAND_MAX;
  double Bin = pow(q,N);
  double Sum = Bin;
  int b=0;
  while (r>=Sum){
    b++;
    if (b>=N)
      printf("b>N");
    Bin*=p/q*(N-b+1)/b;
    Sum+=Bin;
  }
  return b;
}

int binomialLog(int N,double p){
  double q=1-p;
  double r = (double) rand()/RAND_MAX;
  double LBin = N*log(q);
  double Sum = exp(LBin);
  int b=0;
  while (r>=Sum){
    b++;
    if (b>N)
      printf("b>N");
    LBin+=log(p/q*(N-b+1)/b);
    Sum+=exp(LBin);
  }
  return b;
}

int GSL(int N, double i){
  int b=gsl_ran_binomial(RANDOM, i, N);
  return b;
}
  
  

void binomialGenerate(int N, int i){
  double p=pp[i];
  double q = 1-p;
  double LBin = N*log(q);
  double Sum = exp(LBin);
  int b=0;
  while (Sum<0.25){
    b++;
    LBin+=log(p/q*(N-b+1)/b);
    Sum+=exp(LBin);
  }
  Lookup[i][N].LBquarter=exp(LBin);
  Lookup[i][N].bquarter=b;
  Lookup[i][N].Sumquarter=Sum;
  while (Sum<0.5){
    b++;
    LBin+=log(p/q*(N-b+1)/b);
    Sum+=exp(LBin);
  }
  Lookup[i][N].LBhalf=exp(LBin);
  Lookup[i][N].bhalf=b;
  Lookup[i][N].Sumhalf=Sum;
  while (Sum<0.75){
    b++;
    LBin+=log(p/q*(N-b+1)/b);
    Sum+=exp(LBin);
  }
  Lookup[i][N].LB3quarter=exp(LBin);
  Lookup[i][N].b3quarter=b;
  Lookup[i][N].Sum3quarter=Sum;
}

int binomialLookup(int N, int i){
  double p=pp[i];
  double q=1-p;
  if (Lookup[i][N].bhalf<0) {
	binomialGenerate(N,i);
  }
  double Sumhalf=Lookup[i][N].Sumhalf;
  double Sumquarter=Lookup[i][N].Sumquarter;
  double Sum3quarter=Lookup[i][N].Sum3quarter;
  double r = (double) rand()/RAND_MAX;
  if (r==0)
    return 0;
  if (r==1)
    return N;
  //check if Sumhalf etc are -1, then run generate THEN check against r
  if (Sumhalf<=r){
    if (r>=Sum3quarter){
      int b=Lookup[i][N].b3quarter;
      double Sum=Lookup[i][N].Sum3quarter;
      double LB=Lookup[i][N].LB3quarter;
      while (Sum<=r){
	b++;
	LB*=p/q*(N-b+1)/b;
	Sum+=LB;
      }
      return b;
    }
    else if (r>=Sumhalf&&r<Sum3quarter){
      if (Sum3quarter-r<=r-Sumhalf){
	int b=Lookup[i][N].b3quarter;
	double Sum=Lookup[i][N].Sum3quarter;
	double LB=Lookup[i][N].LB3quarter;
	while (r<Sum){
	  b--;
	  Sum-=LB;
	  LB/=p/q*(N-b)/(b+1);
	}
	return b+1;
      }
      else if(Sum3quarter-r>r-Sumhalf){
	int b=Lookup[i][N].bhalf;
	double Sum=Lookup[i][N].Sumhalf;
	double LB=Lookup[i][N].LBhalf;
	while (Sum<=r){
	  b++;
	  LB*=p/q*(N-b+1)/b;
	  Sum+=LB;
	}
	return b;
      }
    }
  }
  else{
    if (r<=Sumquarter){
      int b=Lookup[i][N].bquarter;
      double Sum=Lookup[i][N].Sumquarter;
      double LB=Lookup[i][N].LBquarter;
      while (r<Sum){
	b--;
	Sum-=LB;
	LB/=p/q*(N-b)/(b+1);
      }
      return b+1;
    }
    else if (r>Sumquarter&&r<Sumhalf){
      if (Sumhalf-r<=r-Sumquarter){
	int b=Lookup[i][N].bhalf;
	double Sum=Lookup[i][N].Sumhalf;
	double LB=Lookup[i][N].LBhalf;
	while (r<Sum){
	  b--;
	  Sum-=LB;
	  LB/=p/q*(N-b)/(b+1);
	}
	return b+1;
      }
      else if(Sumhalf-r>r-Sumquarter){
	int b=Lookup[i][N].bquarter;
	double Sum=Lookup[i][N].Sumquarter;
	double LB=Lookup[i][N].LBquarter;
	while (Sum<=r){
	  b++;
	  LB*=p/q*(N-b+1)/b;
	  Sum+=LB;
	}
	return b;
      }
      else
	printf("Error, BinomialLookup does not Terminate Properly");
    }
  }
}

void binomialGenerate5Pt(int N, int i){
  double p=pp[i];
  double q = 1-p;
  double LBin = N*log(q);
  double Sum = exp(LBin);
  int b=0;
  while (Sum<0.15){
    b++;
    LBin+=log(p/q*(N-b+1)/b);
    Sum+=exp(LBin);
  }
  Lookup5Pt[i][N].LB15=exp(LBin);
  Lookup5Pt[i][N].b15=b;
  Lookup5Pt[i][N].Sum15=Sum;
  while (Sum<0.30){
    b++;
    LBin+=log(p/q*(N-b+1)/b);
    Sum+=exp(LBin);
  }
  Lookup5Pt[i][N].LB30=exp(LBin);
  Lookup5Pt[i][N].b30=b;
  Lookup5Pt[i][N].Sum30=Sum;
  while (Sum<0.50){
    b++;
    LBin+=log(p/q*(N-b+1)/b);
    Sum+=exp(LBin);
  }
  Lookup5Pt[i][N].LB50=exp(LBin);
  Lookup5Pt[i][N].b50=b;
  Lookup5Pt[i][N].Sum50=Sum;
  while (Sum<0.70){
    b++;
    LBin+=log(p/q*(N-b+1)/b);
    Sum+=exp(LBin);
  }
  Lookup5Pt[i][N].LB70=exp(LBin);
  Lookup5Pt[i][N].b70=b;
  Lookup5Pt[i][N].Sum70=Sum;
  while (Sum<0.85){
    b++;
    LBin+=log(p/q*(N-b+1)/b);
    Sum+=exp(LBin);
  }
  Lookup5Pt[i][N].LB85=exp(LBin);
  Lookup5Pt[i][N].b85=b;
  Lookup5Pt[i][N].Sum85=Sum;
}

int BinomialLookup5Pt(int N, int i){
  double p=pp[i];
  double q=1-p;
  if (Lookup5Pt[i][N].b50<0) {
	binomialGenerate5Pt(N,i);
  }
  double Sum15=Lookup5Pt[i][N].Sum15;
  double Sum30=Lookup5Pt[i][N].Sum30;
  double Sum50=Lookup5Pt[i][N].Sum50;
  double Sum70=Lookup5Pt[i][N].Sum70;
  double Sum85=Lookup5Pt[i][N].Sum85;
  double r = (double) rand()/RAND_MAX;
  if (r==0)
    return 0;
  else if (r==1)
    return N;
  else{
    int k=0;
    double SumStart=0;
    double SumArray[10]= {Sum15, (Sum15+Sum30)/2, Sum30, (Sum30+Sum50)/2, Sum50, (Sum50+Sum70)/2, Sum70, (Sum70+Sum85)/2, Sum85, 1};
    double LBArray[9]={Lookup5Pt[i][N].LB15, 0,  Lookup5Pt[i][N].LB30, 0,  Lookup5Pt[i][N].LB50, 0,  Lookup5Pt[i][N].LB70, 0, Lookup5Pt[i][N].LB85};
    double bArray[9]={Lookup5Pt[i][N].b15, 0, Lookup5Pt[i][N].b30, 0, Lookup5Pt[i][N].b50, 0, Lookup5Pt[i][N].b70, 0, Lookup5Pt[i][N].b85};
    while((int)(r/SumArray[k])!=0){
      k++;
      SumStart=SumArray[k];
    }
    if(k==0){
      SumStart=Sum15;
      int b=Lookup5Pt[i][N].b15;
      double LB=Lookup5Pt[i][N].LB15;
      while(r<SumStart){
	b--;
	if (b<-1){
	  printf("b>0 THIS SHOULD NOT HAPPEN b= %i N= %i p= %e Sum= %e r= %e \n", b, N, p, SumStart, r);
	}
	SumStart-=LB;
	LB/=p/q*(N-b)/(b+1);
      }
      return b+1;
    }
    else if(k==1||k==3||k==5||k==7||k==9/*SumStart<=SumArray[0] || SumStart<=SumArray[2] || SumStart<=SumArray[4] || SumStart<=SumArray[6] || SumStart<=SumArray[8]*/){
      int b=bArray[k-1];
      double Sum=SumArray[k-1];
      double LB=LBArray[k-1];
      while (Sum<=r){
	b++;
	if (b>N){
	  printf("b>N THIS SHOULD NOT HAPPEN b= %i N= %i p= %e Sum= %e r= %e \n", b, N, p, Sum, r);
	}
	LB*=p/q*(N-b+1)/b;
	Sum+=LB;
      }
      return b;
    }
     else if(k==2||k==4||k==6||k==8/*SumStart<=SumArray[1] || SumStart<=SumArray[3] || SumStart<=SumArray[5] || SumStart<=SumArray[7]*/){
       int b=bArray[k];
       double Sum=SumArray[k];
       double LB=LBArray[k];
       while (r<SumStart){
	 b--;
	 if (b<-1){
	   printf("b>0 THIS SHOULD NOT HAPPEN b= %i N= %i p= %e Sum= %e r= %e \n", b, N, p, SumStart, r);
	 }
	 SumStart-=LB;
	 LB/=p/q*(N-b)/(b+1);
       }
       return b+1;
     }
  }
}

void binomialGenerate7Pt(int N, int i){
  double p=pp[i];
  double q = 1-p;
  double LBin = N*log(q);
  double Sum = exp(LBin);
  int b=0;
  while (Sum<0.10){
    b++;
    LBin+=log(p/q*(N-b+1)/b);
    Sum+=exp(LBin);
  }
  Lookup7Pt[i][N].LB10=exp(LBin);
  Lookup7Pt[i][N].b10=b;
  Lookup7Pt[i][N].Sum10=Sum;
  while (Sum<0.20){
    b++;
    LBin+=log(p/q*(N-b+1)/b);
    Sum+=exp(LBin);
  }
  Lookup7Pt[i][N].LB20=exp(LBin);
  Lookup7Pt[i][N].b20=b;
  Lookup7Pt[i][N].Sum20=Sum;
  while (Sum<0.30){
    b++;
    LBin+=log(p/q*(N-b+1)/b);
    Sum+=exp(LBin);
  }
  Lookup7Pt[i][N].LB30=exp(LBin);
  Lookup7Pt[i][N].b30=b;
  Lookup7Pt[i][N].Sum30=Sum;
  while (Sum<0.50){
    b++;
    LBin+=log(p/q*(N-b+1)/b);
    Sum+=exp(LBin);
  }
  Lookup7Pt[i][N].LB50=exp(LBin);
  Lookup7Pt[i][N].b50=b;
  Lookup7Pt[i][N].Sum50=Sum;
  while (Sum<0.70){
    b++;
    LBin+=log(p/q*(N-b+1)/b);
    Sum+=exp(LBin);
  }
  Lookup7Pt[i][N].LB70=exp(LBin);
  Lookup7Pt[i][N].b70=b;
  Lookup7Pt[i][N].Sum70=Sum;
  while (Sum<0.80){
    b++;
    LBin+=log(p/q*(N-b+1)/b);
    Sum+=exp(LBin);
  }
  Lookup7Pt[i][N].LB80=exp(LBin);
  Lookup7Pt[i][N].b80=b;
  Lookup7Pt[i][N].Sum80=Sum;
  while (Sum<0.90){
    b++;
    LBin+=log(p/q*(N-b+1)/b);
    Sum+=exp(LBin);
  }
  Lookup7Pt[i][N].LB90=exp(LBin);
  Lookup7Pt[i][N].b90=b;
  Lookup7Pt[i][N].Sum90=Sum;
}

int BinomialLookup7Pt(int N, int i){
  double p=pp[i];
  double q=1-p;
  if (Lookup7Pt[i][N].b50<0) {
	binomialGenerate7Pt(N,i);
  }
  double Sum10=Lookup7Pt[i][N].Sum10;
  double Sum20=Lookup7Pt[i][N].Sum20;
  double Sum30=Lookup7Pt[i][N].Sum30;
  double Sum50=Lookup7Pt[i][N].Sum50;
  double Sum70=Lookup7Pt[i][N].Sum70;
  double Sum80=Lookup7Pt[i][N].Sum80;
  double Sum90=Lookup7Pt[i][N].Sum90;
  
  double r = (double) rand()/RAND_MAX;
  if (r==0)
    return 0;
  else if (r==1)
    return N;
  else{
    int k=0;
    double SumStart=0;
    double SumArray[14]= {Sum10, (Sum10+Sum20)/2, Sum20, (Sum20+Sum30)/2, Sum30, (Sum30+Sum50)/2, Sum50, (Sum50+Sum70)/2, Sum70, (Sum70+Sum80)/2, Sum80, (Sum80+Sum90)/2, Sum90, 1};
    double LBArray[13]={Lookup7Pt[i][N].LB10, 0,  Lookup7Pt[i][N].LB20, 0,  Lookup7Pt[i][N].LB30, 0,  Lookup7Pt[i][N].LB50, 0, Lookup7Pt[i][N].LB70, 0, Lookup7Pt[i][N].LB80, 0, Lookup7Pt[i][N].LB90};
    double bArray[13]={Lookup7Pt[i][N].b10, 0, Lookup7Pt[i][N].b20, 0, Lookup7Pt[i][N].b30, 0, Lookup7Pt[i][N].b50, 0, Lookup7Pt[i][N].b70, 0,  Lookup7Pt[i][N].b80, 0,  Lookup7Pt[i][N].b90};
    while((int)(r/SumArray[k])!=0){
      k++;
      SumStart=SumArray[k];
    }
    if(k==0){
      SumStart=Sum10;
      int b=Lookup7Pt[i][N].b10;
      double LB=Lookup7Pt[i][N].LB10;
      while(r<SumStart){
	b--;
	if (b<-1){
	  printf("b>0 THIS SHOULD NOT HAPPEN b= %i N= %i p= %e Sum= %e r= %e \n", b, N, p, SumStart, r);
	}
	SumStart-=LB;
	LB/=p/q*(N-b)/(b+1);
      }
      return b+1;
    }
    else if(k==1||k==3||k==5||k==7||k==9||k==11||k==13/*SumStart<=SumArray[0] || SumStart<=SumArray[2] || SumStart<=SumArray[4] || SumStart<=SumArray[6] || SumStart<=SumArray[8]*/){
      int b=bArray[k-1];
      double Sum=SumArray[k-1];
      double LB=LBArray[k-1];
      while (Sum<=r){
	b++;
	LB*=p/q*(N-b+1)/b;
	Sum+=LB;
      }
      return b;
    }
     else if(k==2||k==4||k==6||k==8||k==10||k==12/*SumStart<=SumArray[1] || SumStart<=SumArray[3] || SumStart<=SumArray[5] || SumStart<=SumArray[7]*/){
               int b=bArray[k];
       double Sum=SumArray[k];
       double LB=LBArray[k];
       while (r<SumStart){
	 b--;
	 SumStart-=LB;
	 LB/=p/q*(N-b)/(b+1);
       }
       //printf("b=%i \n", b+1);
       return b+1;
     }
  }
}

void init(){
  int lookupSize[VPlus], lookupSize5Pt[VPlus], lookupSize7Pt[VPlus];
  double wcum[V];
  /* some GSL types for binomial*/
  gsl_rng_env_setup();
  TYPE=gsl_rng_default;
  RANDOM=gsl_rng_alloc(TYPE);
  //Set up cumulative weights
  wcum[0]=w[0];
  for (int i=1; i<V; i++) {
    wcum[i]=wcum[i-1]+w[i];
    pp[i]=w[i]/wcum[i];
  }
  //Initialize the partial probabiluty array to include Omega (1/Tau)
  pp[V]= (double)1./Tau;
  //Initialize the Structures
  for (int v=0; v<=V; v++) {
    lookupSize[v]=3*Nav+30;
    Lookup[v]=realloc(Lookup[v],lookupSize[v]*sizeof(BinArray_t));
    for (int j=0; j<lookupSize[v]; j++){
      Lookup[v][j].bhalf=-1;
    }
    lookupSize5Pt[v]=5*Nav+50;
    Lookup5Pt[v]=realloc(Lookup5Pt[v],lookupSize5Pt[v]*sizeof(BinArray_5t));
    for (int j=0; j<lookupSize5Pt[v]; j++){
      Lookup5Pt[v][j].b50=-1;
    }
    lookupSize7Pt[v]=7*Nav+70;
    Lookup7Pt[v]=realloc(Lookup7Pt[v],lookupSize7Pt[v]*sizeof(BinArray_7t));
    for (int j=0; j<lookupSize7Pt[v]; j++){
      Lookup7Pt[v][j].b50=-1;
    }
  }
  //Initialize the Particles
  for (int y=0; y<ydim; y++){
    for (int x=0; x<xdim; x++){
      for (int v=0; v<9;v++){
	double lam=Nav*(1+sin(2*M_PI*x/xdim))*w[v];
	n[v][x][y]=poissonLog(lam);	
      }
    }
  }
  iterations=0;
}

void iterateCollisionSet(){
  int NI=0;
  double wcum[V];
  wcum[0]=w[0];
  for (int i=1; i<V; i++) {
    wcum[i]=wcum[i-1]+w[i];
  }
  for (int x=0; x<xdim; x++){
    for (int y=0; y<ydim; y++){
      NI=0;
      for (int v=0; v<V; v++) NI+=n[v][x][y];
      // first implementation: random collisions
      if (NI>0){
	for (int c=0; c<C; c++){
	  int r1=rand()%NI;
	  int v1=0,v2=0;
	  for (; r1>=n[v1][x][y];v1++)
	    r1-=n[v1][x][y];
	  double vc=(double) rand()/RAND_MAX;
	  for (; vc>wcum[v2];v2++);
	  
	  n[v1][x][y]--;
	  n[v2][x][y]++;
	}
      }
    }
  }
  // Streaming
  int tmpx[xdim],tmpy[ydim];
  for (int v=0; v<V; v++){
    int vxs=0,vys=0,vx,vy;
    int vxd=vx=v%3-1;
    if (vxd<0) {vxs=-vxd;vxd=0;}
    int vyd=vy=v/3-1;
    if (vyd<0) {vys=-vyd; vyd=0;}
    
    if (vxd>0)      for (int y=0; y<ydim; y++) tmpy[y]=n[v][xdim-1][y];
    else if (vxs>0) for (int y=0; y<ydim; y++) tmpy[y]=n[v][0][y];
    if (vyd>0)      for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][ydim-1];
    else if (vys>0) for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][0];
    
    memmove(&n[v][vxd][vyd],&n[v][vxs][vys],((xdim-(vxs+vxd))*ydim-(vys+vyd))*sizeof(int));
    
    if (vxd>0)      for (int y=0; y<ydim; y++) n[v][0][y]=     tmpy[(y-vy+ydim)%ydim];
    else if (vxs>0) for (int y=0; y<ydim; y++) n[v][xdim-1][y]=tmpy[(y-vy+ydim)%ydim];
    if (vyd>0)      for (int x=0; x<xdim; x++) n[v][x][0]=     tmpx[(x-vx+xdim)%xdim];
    else if (vys>0) for (int x=0; x<xdim; x++) n[v][x][ydim-1]=tmpx[(x-vx+xdim)%xdim];
  }
}

void iterateCollisionTau(){
  int NI=0;
  double wcum[V];
  wcum[0]=w[0];
  for (int i=1; i<V; i++) {
    wcum[i]=wcum[i-1]+w[i];
  }
  for (int x=0; x<xdim; x++){
    for (int y=0; y<ydim; y++){
      NI=0;
      for (int v=0; v<V; v++) NI+=n[v][x][y];
       // first implementation: random collisions
      if (NI>0){
	C=(int)(-NI*log(1-1/Tau));
	for (int c=0; c<C; c++){
	  int r1=rand()%NI;
	  int v1=0,v2=0;
	  for (; r1>=n[v1][x][y];v1++)
	    r1-=n[v1][x][y];
	  double vc=(double) rand()/RAND_MAX;
	  for (; vc>wcum[v2];v2++);
	  
	  n[v1][x][y]--;
	  n[v2][x][y]++;
	}
      }
    }
  }
  // Streaming
  int tmpx[xdim],tmpy[ydim];
  for (int v=0; v<V; v++){
    int vxs=0,vys=0,vx,vy;
    int vxd=vx=v%3-1;
    if (vxd<0) {vxs=-vxd;vxd=0;}
    int vyd=vy=v/3-1;
    if (vyd<0) {vys=-vyd; vyd=0;}
    
    if (vxd>0)      for (int y=0; y<ydim; y++) tmpy[y]=n[v][xdim-1][y];
    else if (vxs>0) for (int y=0; y<ydim; y++) tmpy[y]=n[v][0][y];
    if (vyd>0)      for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][ydim-1];
    else if (vys>0) for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][0];
    
    memmove(&n[v][vxd][vyd],&n[v][vxs][vys],((xdim-(vxs+vxd))*ydim-(vys+vyd))*sizeof(int));
    
    if (vxd>0)      for (int y=0; y<ydim; y++) n[v][0][y]=     tmpy[(y-vy+ydim)%ydim];
    else if (vxs>0) for (int y=0; y<ydim; y++) n[v][xdim-1][y]=tmpy[(y-vy+ydim)%ydim];
    if (vyd>0)      for (int x=0; x<xdim; x++) n[v][x][0]=     tmpx[(x-vx+xdim)%xdim];
    else if (vys>0) for (int x=0; x<xdim; x++) n[v][x][ydim-1]=tmpx[(x-vx+xdim)%xdim];
  }
}

void iterateSample(){
  int NI=0;
  double wcum[V];
  wcum[0]=w[0];
  for (int i=1; i<V; i++) {
    wcum[i]=wcum[i-1]+w[i];
  }
  for (int x=0; x<xdim; x++){
    for (int y=0; y<ydim; y++){
      NI=0;
      for (int v=0; v<V; v++) NI+=n[v][x][y];
      //Sampling Function Call
      if (NI>0){
	for (int v=V-1; v>0; v--){
	  int b=binomialLog(NI,pp[v]);
	  n[v][x][y]=b+NILeft[v];
	  NI-=b;
	}
	n[0][x][y]=NI+NILeft[0];
      }
    }
  }
  // Streaming
  int tmpx[xdim],tmpy[ydim];
  for (int v=0; v<V; v++){
    int vxs=0,vys=0,vx,vy;
    int vxd=vx=v%3-1;
    if (vxd<0) {vxs=-vxd;vxd=0;}
    int vyd=vy=v/3-1;
    if (vyd<0) {vys=-vyd; vyd=0;}
    
    if (vxd>0)      for (int y=0; y<ydim; y++) tmpy[y]=n[v][xdim-1][y];
    else if (vxs>0) for (int y=0; y<ydim; y++) tmpy[y]=n[v][0][y];
    if (vyd>0)      for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][ydim-1];
    else if (vys>0) for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][0];
    
    memmove(&n[v][vxd][vyd],&n[v][vxs][vys],((xdim-(vxs+vxd))*ydim-(vys+vyd))*sizeof(int));
    
    if (vxd>0)      for (int y=0; y<ydim; y++) n[v][0][y]=     tmpy[(y-vy+ydim)%ydim];
    else if (vxs>0) for (int y=0; y<ydim; y++) n[v][xdim-1][y]=tmpy[(y-vy+ydim)%ydim];
    if (vyd>0)      for (int x=0; x<xdim; x++) n[v][x][0]=     tmpx[(x-vx+xdim)%xdim];
    else if (vys>0) for (int x=0; x<xdim; x++) n[v][x][ydim-1]=tmpx[(x-vx+xdim)%xdim];
  }
}

void iterateSampleTau(){
  int NI=0;
  double wcum[V];
  wcum[0]=w[0];
  for (int i=1; i<V; i++) {
    wcum[i]=wcum[i-1]+w[i];
  }
  for (int x=0; x<xdim; x++){
    for (int y=0; y<ydim; y++){
      // Sampling for Tau > 1
      NI=0;
      int NIb=0;
      for (int v=0; v<V; v++)
	NILeft[v]=0;
      for (int v=0; v<V; v++){
	NIb = binomialLog(n[v][x][y],pp[V]);
	NI+=NIb;
	NILeft[v]=n[v][x][y]-NIb;
      }
      // Sampling Function Call
      if (NI>0){
	for (int v=V-1; v>0; v--){
	  int b=binomialLog(NI,pp[v]);
	  n[v][x][y]=b+NILeft[v];
	  NI-=b;
	}
	n[0][x][y]=NI+NILeft[0];
      }
    }
  }
  // Streaming
  int tmpx[xdim],tmpy[ydim];
  for (int v=0; v<V; v++){
    int vxs=0,vys=0,vx,vy;
    int vxd=vx=v%3-1;
    if (vxd<0) {vxs=-vxd;vxd=0;}
    int vyd=vy=v/3-1;
    if (vyd<0) {vys=-vyd; vyd=0;}
    
    if (vxd>0)      for (int y=0; y<ydim; y++) tmpy[y]=n[v][xdim-1][y];
    else if (vxs>0) for (int y=0; y<ydim; y++) tmpy[y]=n[v][0][y];
    if (vyd>0)      for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][ydim-1];
    else if (vys>0) for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][0];
    
    memmove(&n[v][vxd][vyd],&n[v][vxs][vys],((xdim-(vxs+vxd))*ydim-(vys+vyd))*sizeof(int));
    
    if (vxd>0)      for (int y=0; y<ydim; y++) n[v][0][y]=     tmpy[(y-vy+ydim)%ydim];
    else if (vxs>0) for (int y=0; y<ydim; y++) n[v][xdim-1][y]=tmpy[(y-vy+ydim)%ydim];
    if (vyd>0)      for (int x=0; x<xdim; x++) n[v][x][0]=     tmpx[(x-vx+xdim)%xdim];
    else if (vys>0) for (int x=0; x<xdim; x++) n[v][x][ydim-1]=tmpx[(x-vx+xdim)%xdim];
  }
}

void iterate3Pt(){
  int NI=0;
  double wcum[V];
  wcum[0]=w[0];
  for (int i=1; i<V; i++) {
    wcum[i]=wcum[i-1]+w[i];
  }
  for (int x=0; x<xdim; x++){
    for (int y=0; y<ydim; y++){
      NI=0;
      for (int v=0; v<V; v++) NI+=n[v][x][y];
      //Sampling Function Call
      if (NI>0){
	for (int v=V-1; v>0; v--){
	  int b=binomialLookup(NI,v);
	  n[v][x][y]=b+NILeft[v];
	  NI-=b;
	}
	n[0][x][y]=NI+NILeft[0];
      }
    }
  }
  // Streaming
  int tmpx[xdim],tmpy[ydim];
  for (int v=0; v<V; v++){
    int vxs=0,vys=0,vx,vy;
    int vxd=vx=v%3-1;
    if (vxd<0) {vxs=-vxd;vxd=0;}
    int vyd=vy=v/3-1;
    if (vyd<0) {vys=-vyd; vyd=0;}
    
    if (vxd>0)      for (int y=0; y<ydim; y++) tmpy[y]=n[v][xdim-1][y];
    else if (vxs>0) for (int y=0; y<ydim; y++) tmpy[y]=n[v][0][y];
    if (vyd>0)      for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][ydim-1];
    else if (vys>0) for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][0];
    
    memmove(&n[v][vxd][vyd],&n[v][vxs][vys],((xdim-(vxs+vxd))*ydim-(vys+vyd))*sizeof(int));
    
    if (vxd>0)      for (int y=0; y<ydim; y++) n[v][0][y]=     tmpy[(y-vy+ydim)%ydim];
    else if (vxs>0) for (int y=0; y<ydim; y++) n[v][xdim-1][y]=tmpy[(y-vy+ydim)%ydim];
    if (vyd>0)      for (int x=0; x<xdim; x++) n[v][x][0]=     tmpx[(x-vx+xdim)%xdim];
    else if (vys>0) for (int x=0; x<xdim; x++) n[v][x][ydim-1]=tmpx[(x-vx+xdim)%xdim];
  }
}

void iterate3PtTau(){
  int NI=0;
  double wcum[V];
  wcum[0]=w[0];
  for (int i=1; i<V; i++) {
    wcum[i]=wcum[i-1]+w[i];
  }
  for (int x=0; x<xdim; x++){
    for (int y=0; y<ydim; y++){
      // Sampling for Tau > 1
      NI=0;
      int NIb=0;
      for (int v=0; v<V; v++)
	NILeft[v]=0;
      for (int v=0; v<V; v++){
	NIb = binomialLookup(n[v][x][y],V);
	NI+=NIb;
	NILeft[v]=n[v][x][y]-NIb;
      }
      // Sampling Function Call
      if (NI>0){
	for (int v=V-1; v>0; v--){
	  int b=binomialLookup(NI,v);
	  n[v][x][y]=b+NILeft[v];
	  NI-=b;
	}
	n[0][x][y]=NI+NILeft[0];
      }
    }
  }
  // Streaming
  int tmpx[xdim],tmpy[ydim];
  for (int v=0; v<V; v++){
    int vxs=0,vys=0,vx,vy;
    int vxd=vx=v%3-1;
    if (vxd<0) {vxs=-vxd;vxd=0;}
    int vyd=vy=v/3-1;
    if (vyd<0) {vys=-vyd; vyd=0;}
    
    if (vxd>0)      for (int y=0; y<ydim; y++) tmpy[y]=n[v][xdim-1][y];
    else if (vxs>0) for (int y=0; y<ydim; y++) tmpy[y]=n[v][0][y];
    if (vyd>0)      for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][ydim-1];
    else if (vys>0) for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][0];
    
    memmove(&n[v][vxd][vyd],&n[v][vxs][vys],((xdim-(vxs+vxd))*ydim-(vys+vyd))*sizeof(int));
    
    if (vxd>0)      for (int y=0; y<ydim; y++) n[v][0][y]=     tmpy[(y-vy+ydim)%ydim];
    else if (vxs>0) for (int y=0; y<ydim; y++) n[v][xdim-1][y]=tmpy[(y-vy+ydim)%ydim];
    if (vyd>0)      for (int x=0; x<xdim; x++) n[v][x][0]=     tmpx[(x-vx+xdim)%xdim];
    else if (vys>0) for (int x=0; x<xdim; x++) n[v][x][ydim-1]=tmpx[(x-vx+xdim)%xdim];
  }
}

void iterate5Pt(){
  int NI=0;
  double wcum[V];
  wcum[0]=w[0];
  for (int i=1; i<V; i++) {
    wcum[i]=wcum[i-1]+w[i];
  }
  for (int x=0; x<xdim; x++){
    for (int y=0; y<ydim; y++){
      NI=0;
      for (int v=0; v<V; v++) NI+=n[v][x][y];
      //Sampling Function Call
      if (NI>0){
	for (int v=V-1; v>0; v--){
	  int b=BinomialLookup5Pt(NI,v);
	  n[v][x][y]=b+NILeft[v];
	  NI-=b;
	}
	n[0][x][y]=NI+NILeft[0];
      }
    }
  }
  // Streaming
  int tmpx[xdim],tmpy[ydim];
  for (int v=0; v<V; v++){
    int vxs=0,vys=0,vx,vy;
    int vxd=vx=v%3-1;
    if (vxd<0) {vxs=-vxd;vxd=0;}
    int vyd=vy=v/3-1;
    if (vyd<0) {vys=-vyd; vyd=0;}
    
    if (vxd>0)      for (int y=0; y<ydim; y++) tmpy[y]=n[v][xdim-1][y];
    else if (vxs>0) for (int y=0; y<ydim; y++) tmpy[y]=n[v][0][y];
    if (vyd>0)      for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][ydim-1];
    else if (vys>0) for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][0];
    
    memmove(&n[v][vxd][vyd],&n[v][vxs][vys],((xdim-(vxs+vxd))*ydim-(vys+vyd))*sizeof(int));
    
    if (vxd>0)      for (int y=0; y<ydim; y++) n[v][0][y]=     tmpy[(y-vy+ydim)%ydim];
    else if (vxs>0) for (int y=0; y<ydim; y++) n[v][xdim-1][y]=tmpy[(y-vy+ydim)%ydim];
    if (vyd>0)      for (int x=0; x<xdim; x++) n[v][x][0]=     tmpx[(x-vx+xdim)%xdim];
    else if (vys>0) for (int x=0; x<xdim; x++) n[v][x][ydim-1]=tmpx[(x-vx+xdim)%xdim];
  }
}

void iterate5PtTau(){
  int NI=0;
  double wcum[V];
  wcum[0]=w[0];
  for (int i=1; i<V; i++) {
    wcum[i]=wcum[i-1]+w[i];
  }
  for (int x=0; x<xdim; x++){
    for (int y=0; y<ydim; y++){
      // Sampling for Tau > 1
      NI=0;
      int NIb=0;
      for (int v=0; v<V; v++)
	NILeft[v]=0;
      for (int v=0; v<V; v++){
	NIb = BinomialLookup5Pt(n[v][x][y],V);
	NI+=NIb;
	NILeft[v]=n[v][x][y]-NIb;
      }
      // Sampling Function Call
      if (NI>0){
	for (int v=V-1; v>0; v--){
	  int b=BinomialLookup5Pt(NI,v);
	  n[v][x][y]=b+NILeft[v];
	  NI-=b;
	}
	n[0][x][y]=NI+NILeft[0];
      }
    }
  }
  // Streaming
  int tmpx[xdim],tmpy[ydim];
  for (int v=0; v<V; v++){
    int vxs=0,vys=0,vx,vy;
    int vxd=vx=v%3-1;
    if (vxd<0) {vxs=-vxd;vxd=0;}
    int vyd=vy=v/3-1;
    if (vyd<0) {vys=-vyd; vyd=0;}
    
    if (vxd>0)      for (int y=0; y<ydim; y++) tmpy[y]=n[v][xdim-1][y];
    else if (vxs>0) for (int y=0; y<ydim; y++) tmpy[y]=n[v][0][y];
    if (vyd>0)      for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][ydim-1];
    else if (vys>0) for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][0];
    
    memmove(&n[v][vxd][vyd],&n[v][vxs][vys],((xdim-(vxs+vxd))*ydim-(vys+vyd))*sizeof(int));
    
    if (vxd>0)      for (int y=0; y<ydim; y++) n[v][0][y]=     tmpy[(y-vy+ydim)%ydim];
    else if (vxs>0) for (int y=0; y<ydim; y++) n[v][xdim-1][y]=tmpy[(y-vy+ydim)%ydim];
    if (vyd>0)      for (int x=0; x<xdim; x++) n[v][x][0]=     tmpx[(x-vx+xdim)%xdim];
    else if (vys>0) for (int x=0; x<xdim; x++) n[v][x][ydim-1]=tmpx[(x-vx+xdim)%xdim];
  }
}

void iterate7Pt(){
  int NI=0;
  double wcum[V];
  wcum[0]=w[0];
  for (int i=1; i<V; i++) {
    wcum[i]=wcum[i-1]+w[i];
  }
  for (int x=0; x<xdim; x++){
    for (int y=0; y<ydim; y++){
      NI=0;
      for (int v=0; v<V; v++) NI+=n[v][x][y];
      //Sampling Function Call
      if (NI>0){
	for (int v=V-1; v>0; v--){
	  int b=BinomialLookup7Pt(NI,v);
	  n[v][x][y]=b+NILeft[v];
	  NI-=b;
	}
	n[0][x][y]=NI+NILeft[0];
      }
    }
  }
  // Streaming
  int tmpx[xdim],tmpy[ydim];
  for (int v=0; v<V; v++){
    int vxs=0,vys=0,vx,vy;
    int vxd=vx=v%3-1;
    if (vxd<0) {vxs=-vxd;vxd=0;}
    int vyd=vy=v/3-1;
    if (vyd<0) {vys=-vyd; vyd=0;}
    
    if (vxd>0)      for (int y=0; y<ydim; y++) tmpy[y]=n[v][xdim-1][y];
    else if (vxs>0) for (int y=0; y<ydim; y++) tmpy[y]=n[v][0][y];
    if (vyd>0)      for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][ydim-1];
    else if (vys>0) for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][0];
    
    memmove(&n[v][vxd][vyd],&n[v][vxs][vys],((xdim-(vxs+vxd))*ydim-(vys+vyd))*sizeof(int));
    
    if (vxd>0)      for (int y=0; y<ydim; y++) n[v][0][y]=     tmpy[(y-vy+ydim)%ydim];
    else if (vxs>0) for (int y=0; y<ydim; y++) n[v][xdim-1][y]=tmpy[(y-vy+ydim)%ydim];
    if (vyd>0)      for (int x=0; x<xdim; x++) n[v][x][0]=     tmpx[(x-vx+xdim)%xdim];
    else if (vys>0) for (int x=0; x<xdim; x++) n[v][x][ydim-1]=tmpx[(x-vx+xdim)%xdim];
  }
}

void iterate7PtTau(){
  int NI=0;
  double wcum[V];
  wcum[0]=w[0];
  for (int i=1; i<V; i++) {
    wcum[i]=wcum[i-1]+w[i];
  }
  for (int x=0; x<xdim; x++){
    for (int y=0; y<ydim; y++){
      // Sampling for Tau > 1
      NI=0;
      int NIb=0;
      for (int v=0; v<V; v++)
	NILeft[v]=0;
      for (int v=0; v<V; v++){
	NIb = BinomialLookup7Pt(n[v][x][y],V);
	NI+=NIb;
	NILeft[v]=n[v][x][y]-NIb;
      }
      // Sampling Function Call
      if (NI>0){
	for (int v=V-1; v>0; v--){
	  int b=BinomialLookup7Pt(NI,v);
	  n[v][x][y]=b+NILeft[v];
	  NI-=b;
	}
	n[0][x][y]=NI+NILeft[0];
      }
    }
  }
  // Streaming
  int tmpx[xdim],tmpy[ydim];
  for (int v=0; v<V; v++){
    int vxs=0,vys=0,vx,vy;
    int vxd=vx=v%3-1;
    if (vxd<0) {vxs=-vxd;vxd=0;}
    int vyd=vy=v/3-1;
    if (vyd<0) {vys=-vyd; vyd=0;}
    
    if (vxd>0)      for (int y=0; y<ydim; y++) tmpy[y]=n[v][xdim-1][y];
    else if (vxs>0) for (int y=0; y<ydim; y++) tmpy[y]=n[v][0][y];
    if (vyd>0)      for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][ydim-1];
    else if (vys>0) for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][0];
    
    memmove(&n[v][vxd][vyd],&n[v][vxs][vys],((xdim-(vxs+vxd))*ydim-(vys+vyd))*sizeof(int));
    
    if (vxd>0)      for (int y=0; y<ydim; y++) n[v][0][y]=     tmpy[(y-vy+ydim)%ydim];
    else if (vxs>0) for (int y=0; y<ydim; y++) n[v][xdim-1][y]=tmpy[(y-vy+ydim)%ydim];
    if (vyd>0)      for (int x=0; x<xdim; x++) n[v][x][0]=     tmpx[(x-vx+xdim)%xdim];
    else if (vys>0) for (int x=0; x<xdim; x++) n[v][x][ydim-1]=tmpx[(x-vx+xdim)%xdim];
  }
}

void iterateGSL(){
  int NI=0;
  double wcum[V];
  wcum[0]=w[0];
  for (int i=1; i<V; i++) {
    wcum[i]=wcum[i-1]+w[i];
  }
  for (int x=0; x<xdim; x++){
    for (int y=0; y<ydim; y++){
      NI=0;
      for (int v=0; v<V; v++) NI+=n[v][x][y];
      //Sampling Function Call
      if (NI>0){
	for (int v=V-1; v>0; v--){
	  double p=pp[v];
	  int b=GSL(NI,p);
	  n[v][x][y]=b+NILeft[v];
	  NI-=b;
	}
	n[0][x][y]=NI+NILeft[0];
      }
    }
  }
  // Streaming
  int tmpx[xdim],tmpy[ydim];
  for (int v=0; v<V; v++){
    int vxs=0,vys=0,vx,vy;
    int vxd=vx=v%3-1;
    if (vxd<0) {vxs=-vxd;vxd=0;}
    int vyd=vy=v/3-1;
    if (vyd<0) {vys=-vyd; vyd=0;}
    
    if (vxd>0)      for (int y=0; y<ydim; y++) tmpy[y]=n[v][xdim-1][y];
    else if (vxs>0) for (int y=0; y<ydim; y++) tmpy[y]=n[v][0][y];
    if (vyd>0)      for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][ydim-1];
    else if (vys>0) for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][0];
    
    memmove(&n[v][vxd][vyd],&n[v][vxs][vys],((xdim-(vxs+vxd))*ydim-(vys+vyd))*sizeof(int));
    
    if (vxd>0)      for (int y=0; y<ydim; y++) n[v][0][y]=     tmpy[(y-vy+ydim)%ydim];
    else if (vxs>0) for (int y=0; y<ydim; y++) n[v][xdim-1][y]=tmpy[(y-vy+ydim)%ydim];
    if (vyd>0)      for (int x=0; x<xdim; x++) n[v][x][0]=     tmpx[(x-vx+xdim)%xdim];
    else if (vys>0) for (int x=0; x<xdim; x++) n[v][x][ydim-1]=tmpx[(x-vx+xdim)%xdim];
  }
}

void iterateGSLTau(){
  int NI=0;
  double wcum[V];
  wcum[0]=w[0];
  for (int i=1; i<V; i++) {
    wcum[i]=wcum[i-1]+w[i];
  }
  for (int x=0; x<xdim; x++){
    for (int y=0; y<ydim; y++){
      // Sampling for Tau > 1
      NI=0;
      int NIb=0;
      for (int v=0; v<V; v++)
	NILeft[v]=0;
      for (int v=0; v<V; v++){
	double p=pp[V];
	NIb = GSL(n[v][x][y],p);
	NI+=NIb;
	NILeft[v]=n[v][x][y]-NIb;
      }
      // Sampling Function Call
      if (NI>0){
	for (int v=V-1; v>0; v--){
	  double p=pp[v];
	  int b=GSL(NI,p);
	  n[v][x][y]=b+NILeft[v];
	  NI-=b;
	}
	n[0][x][y]=NI+NILeft[0];
      }
    }
  }
  // Streaming
  int tmpx[xdim],tmpy[ydim];
  for (int v=0; v<V; v++){
    int vxs=0,vys=0,vx,vy;
    int vxd=vx=v%3-1;
    if (vxd<0) {vxs=-vxd;vxd=0;}
    int vyd=vy=v/3-1;
    if (vyd<0) {vys=-vyd; vyd=0;}
    
    if (vxd>0)      for (int y=0; y<ydim; y++) tmpy[y]=n[v][xdim-1][y];
    else if (vxs>0) for (int y=0; y<ydim; y++) tmpy[y]=n[v][0][y];
    if (vyd>0)      for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][ydim-1];
    else if (vys>0) for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][0];
    
    memmove(&n[v][vxd][vyd],&n[v][vxs][vys],((xdim-(vxs+vxd))*ydim-(vys+vyd))*sizeof(int));
    
    if (vxd>0)      for (int y=0; y<ydim; y++) n[v][0][y]=     tmpy[(y-vy+ydim)%ydim];
    else if (vxs>0) for (int y=0; y<ydim; y++) n[v][xdim-1][y]=tmpy[(y-vy+ydim)%ydim];
    if (vyd>0)      for (int x=0; x<xdim; x++) n[v][x][0]=     tmpx[(x-vx+xdim)%xdim];
    else if (vys>0) for (int x=0; x<xdim; x++) n[v][x][ydim-1]=tmpx[(x-vx+xdim)%xdim];
  }
}

void iterateGSLMult(){
  int NI=0;
  double wcum[V];
  wcum[0]=w[0];
  for (int i=1; i<V; i++) {
    wcum[i]=wcum[i-1]+w[i];
  }
  for (int x=0; x<xdim; x++){
    for (int y=0; y<ydim; y++){
      NI=0;
      for (int v=0; v<V; v++) NI+=n[v][x][y];
      // Sampling Function Call
      if (NI>0){
	int nn[V];
	gsl_ran_multinomial(RANDOM,V,NI,w,nn);
	for (int v=0; v<V; v++){
	  n[v][x][y]=nn[v]+NILeft[v];
	}
      }
    }
  }
  // Streaming
  int tmpx[xdim],tmpy[ydim];
  for (int v=0; v<V; v++){
    int vxs=0,vys=0,vx,vy;
    int vxd=vx=v%3-1;
    if (vxd<0) {vxs=-vxd;vxd=0;}
    int vyd=vy=v/3-1;
    if (vyd<0) {vys=-vyd; vyd=0;}
    
    if (vxd>0)      for (int y=0; y<ydim; y++) tmpy[y]=n[v][xdim-1][y];
    else if (vxs>0) for (int y=0; y<ydim; y++) tmpy[y]=n[v][0][y];
    if (vyd>0)      for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][ydim-1];
    else if (vys>0) for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][0];
    
    memmove(&n[v][vxd][vyd],&n[v][vxs][vys],((xdim-(vxs+vxd))*ydim-(vys+vyd))*sizeof(int));
    
    if (vxd>0)      for (int y=0; y<ydim; y++) n[v][0][y]=     tmpy[(y-vy+ydim)%ydim];
    else if (vxs>0) for (int y=0; y<ydim; y++) n[v][xdim-1][y]=tmpy[(y-vy+ydim)%ydim];
    if (vyd>0)      for (int x=0; x<xdim; x++) n[v][x][0]=     tmpx[(x-vx+xdim)%xdim];
    else if (vys>0) for (int x=0; x<xdim; x++) n[v][x][ydim-1]=tmpx[(x-vx+xdim)%xdim];
  }
}

void iterateGSLMultTau(){
  int NI=0;
  double wcum[V];
  wcum[0]=w[0];
  for (int i=1; i<V; i++) {
    wcum[i]=wcum[i-1]+w[i];
  }
  for (int x=0; x<xdim; x++){
    for (int y=0; y<ydim; y++){
      // Sampling for Tau > 1
      NI=0;
      int NIb=0;
      for (int v=0; v<V; v++)
	NILeft[v]=0;
      for (int v=0; v<V; v++){
	double p=pp[V];
	NIb = GSL(n[v][x][y],p);
	NI+=NIb;
	NILeft[v]=n[v][x][y]-NIb;
      }
      // Sampling Function Call
      if (NI>0){
	int nn[V];
	gsl_ran_multinomial(RANDOM,V,NI,w,nn);
	for (int v=0; v<V; v++){
	  n[v][x][y]=nn[v]+NILeft[v];
	}
      }
    }
  }
  // Streaming
  int tmpx[xdim],tmpy[ydim];
  for (int v=0; v<V; v++){
    int vxs=0,vys=0,vx,vy;
    int vxd=vx=v%3-1;
    if (vxd<0) {vxs=-vxd;vxd=0;}
    int vyd=vy=v/3-1;
    if (vyd<0) {vys=-vyd; vyd=0;}
    
    if (vxd>0)      for (int y=0; y<ydim; y++) tmpy[y]=n[v][xdim-1][y];
    else if (vxs>0) for (int y=0; y<ydim; y++) tmpy[y]=n[v][0][y];
    if (vyd>0)      for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][ydim-1];
    else if (vys>0) for (int x=0; x<xdim; x++) tmpx[x]=n[v][x][0];
    
    memmove(&n[v][vxd][vyd],&n[v][vxs][vys],((xdim-(vxs+vxd))*ydim-(vys+vyd))*sizeof(int));
    
    if (vxd>0)      for (int y=0; y<ydim; y++) n[v][0][y]=     tmpy[(y-vy+ydim)%ydim];
    else if (vxs>0) for (int y=0; y<ydim; y++) n[v][xdim-1][y]=tmpy[(y-vy+ydim)%ydim];
    if (vyd>0)      for (int x=0; x<xdim; x++) n[v][x][0]=     tmpx[(x-vx+xdim)%xdim];
    else if (vys>0) for (int x=0; x<xdim; x++) n[v][x][ydim-1]=tmpx[(x-vx+xdim)%xdim];
  }
}

void iterate(){
  if(Tau<=1.){
    if(sample){
      iterateSample();
    }
    else if(lookup){
      iterate3Pt();
    }
    else if(FivePoint){
      iterate5Pt();
    }
    else if(SevenPoint){
      iterate7Pt();
    }
    else if(gsl){
      iterateGSL();
    }
    else if(multinomial){
      iterateGSLMult();
    }
    else{
      iterateCollisionSet();
    }
  }
  else if(collision){
    iterateCollisionSet();
  }
  else{
    if(sample){
      iterateSampleTau();
    }
    else if(lookup){
      iterate3PtTau();
    }
    else if(FivePoint){
      iterate5PtTau();
    }
    else if(SevenPoint){
      iterate7PtTau();
    }
    else if(gsl){
      iterateGSLTau();
    }
    else if(multinomial){
      iterateGSLMultTau();
    }
    else{
      iterateCollisionTau();
    }
  }
}


 void getdata(){
  if (NUreq||Nreq||nav_req){
    NUreq=0;
    Nreq=0;
    for (int x=0; x<xdim; x++)
      for (int y=0; y<ydim; y++){
	N[x][y]=0;
	NU[x][y][0]=0;
	NU[x][y][1]=0;
	for (int v=0; v<V; v++){
	  N[x][y]+=n[v][x][y];
	  NU[x][y][0]+=n[v][x][y]*(v%3-1);
	  NU[x][y][1]+=n[v][x][y]*(1-v/3);
	}
      }
  }
  if (nnreq){
    nnreq=0;
    for (int x=0; x<xdim; x++)
      for (int y=0; y<ydim; y++){
	for (int v=0; v<V; v++){
	  nn[v][x][y]=n[v][x][y];
	}
      }
  }
  if (nav_req){
    nav_req=0;
    for (int x=0; x<xdim; x++){
      nav[x]=0;
      for (int y=0; y<ydim; y++){
	nav[x]+=N[x][y];
      }
      nav[x]/=ydim;
    }
  }
  if (nav_th_req){
    nav_th_req=0;
    double D=(Tau-0.5)/3.;
    for (int x=0; x<xdim; x++){
      nav_th[x]=Nav*(1+sin(2*M_PI*x/xdim)*exp(-4*M_PI*M_PI*D/xdim/xdim*iterations));
    }
  }  
}


int main(){
  int done=0,sstep=0,cont=0,repeat=10;
  init();
  DefineGraphNxN_R("N",&N[0][0],&XDIM,&YDIM,&Nreq);
  for (int v=0; v<V; v++)
    DefineGraphNxN_R("nn",&nn[v][0][0],&XDIM,&YDIM,&nnreq);
  DefineGraphNxN_RxR("NU",&NU[0][0][0],&XDIM,&YDIM,&NUreq);

  DefineGraphN_R("nav",&nav[0],&XDIM,&nav_req);
  DefineGraphN_R("nav_th",&nav_th[0],&XDIM,&nav_th_req);
  
  StartMenu("LG",1);
  DefineInt("iterations", &iterations);//Display the total number of iterations
  DefineDouble("Nav",&Nav);//Change the average number of particles in the menu
  DefineDouble("Tau", &Tau);//Change the Tau value in the menu
  DefineFunction("init",init);//Initialize the system
  DefineGraph(contour2d_,"Graph");//Access density graphs
  DefineGraph(curve2d_,"2d graph");//Access 2D graphs
DefineInt("C", &C);//Change the number of collisions per lattice point per timestep
//Enablw different methods
  DefineBool("ThreePoint", &lookup); 
  DefineBool("Sample",&sample);
  DefineBool("GSL",&gsl);
  DefineBool("FivePoint",&FivePoint);
  DefineBool("SevenPoint",&SevenPoint);
  DefineBool("Multinomial", &multinomial);
//Iteration settings
  DefineInt("repeat",&repeat);
  DefineBool("sstep",&sstep);
  DefineBool("cont",&cont);
  DefineBool("done",&done);
  EndMenu();

  while (!done){
    Events(1);
    getdata();
    DrawGraphs();
    if (cont || sstep){
      sstep=0;

      for (int i=0; i<repeat; i++) {
	iterate();
	//setrho();
      }
      iterations+=repeat;
    } else sleep(1);
  }
  return 0;
}
