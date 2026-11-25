/* pqvs.c -- reference implementation of PQVS (short-LSSS + SIS commitments)
 * Validation of the algebra (S1-S3, correctness, privacy-shift identities, attacks)
 * and cost / parameter reporting.  NOT constant time, RNG NOT cryptographic.
 * Field arithmetic uses uint64 with q < 2^62 (unsigned __int128 for products).
 *
 *   ./pqvs validate
 *   ./pqvs bench t n lam_s qbits m k      (builds t-of-n minimal-set DNF, times everything)
 *   ./pqvs plan  t n lam_s qbits m        (closed-form parameters/costs, any qbits, any n)
 */
#define _POSIX_C_SOURCE 200809L
#define _DEFAULT_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <stdarg.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64; typedef int64_t i64; typedef unsigned __int128 u128;

/* ------------------------------------------------------------ RNG */
static u64 rs[4];
static inline u64 rotl(u64 x,int k){return (x<<k)|(x>>(64-k));}
static u64 rnd64(void){u64 r=rotl(rs[1]*5,7)*9,t=rs[1]<<17;rs[2]^=rs[0];rs[3]^=rs[1];rs[1]^=rs[2];rs[0]^=rs[3];rs[2]^=t;rs[3]=rotl(rs[3],45);return r;}
static void seed_rng(u64 s){for(int i=0;i<4;i++){s+=0x9e3779b97f4a7c15ULL;u64 z=s;z=(z^(z>>30))*0xbf58476d1ce4e5b9ULL;z=(z^(z>>27))*0x94d049bb133111ebULL;rs[i]=z^(z>>31);}}
static u64 rnd_below(u64 n){u64 lim=UINT64_MAX-UINT64_MAX%n,r;do r=rnd64();while(r>=lim);return r%n;}

/* ------------------------------------------------------------ Z_q */
static u64 Q;
static inline u64 mulmod(u64 a,u64 b){return (u64)((u128)a*b%Q);}
static inline u64 addmod(u64 a,u64 b){u64 c=a+b;return c>=Q?c-Q:c;}
static inline u64 submod(u64 a,u64 b){return a>=b?a-b:a+Q-b;}
static inline u64 red(i64 x){i64 r=x%(i64)Q;return r<0?(u64)(r+(i64)Q):(u64)r;}
static u64 powmod(u64 a,u64 e,u64 n){u64 r=1;a%=n;while(e){if(e&1)r=(u64)((u128)r*a%n);a=(u64)((u128)a*a%n);e>>=1;}return r;}
static int is_prime(u64 n){
  if(n<2)return 0; static const u64 B[]={2,3,5,7,11,13,17,19,23,29,31,37};
  for(int i=0;i<12;i++){if(n%B[i]==0)return n==B[i];}
  u64 d=n-1;int s=0;while(!(d&1)){d>>=1;s++;}
  for(int i=0;i<12;i++){u64 x=powmod(B[i],d,n);if(x==1||x==n-1)continue;int ok=0;
    for(int r=1;r<s;r++){x=(u64)((u128)x*x%n);if(x==n-1){ok=1;break;}} if(!ok)return 0;}
  return 1;}
static u64 next_prime(u64 n){if(!(n&1))n++;while(!is_prime(n))n+=2;return n;}

/* ------------------------------------------------------------ formulas */
enum{LEAF,AND,OR};
typedef struct Node{int type,party,nch,slot;struct Node**ch;int*fc;}Node;
static Node* leaf(int p){Node*x=calloc(1,sizeof*x);x->type=LEAF;x->party=p;return x;}
static Node* node(int type,Node**ch,int n){Node*x=calloc(1,sizeof*x);x->type=type;x->ch=ch;x->nch=n;return x;}
static Node* gate(int type,int n,...){Node**c=malloc(n*sizeof*c);va_list ap;va_start(ap,n);for(int i=0;i<n;i++)c[i]=va_arg(ap,Node*);va_end(ap);return node(type,c,n);}
static Node* threshold_dnf(int t,int n){
  int cnt=0;for(unsigned m=0;m<(1u<<n);m++)if(__builtin_popcount(m)==t)cnt++;
  Node**cl=malloc(cnt*sizeof*cl);int idx=0;
  for(unsigned m=0;m<(1u<<n);m++)if(__builtin_popcount(m)==t){Node**lv=malloc(t*sizeof*lv);int j=0;
    for(int i=0;i<n;i++)if(m>>i&1)lv[j++]=leaf(i);cl[idx++]=node(AND,lv,t);}
  return node(OR,cl,cnt);}
static int eval(const Node*x,unsigned mask){
  if(x->type==LEAF)return mask>>x->party&1;
  if(x->type==AND){for(int i=0;i<x->nch;i++)if(!eval(x->ch[i],mask))return 0;return 1;}
  for(int i=0;i<x->nch;i++)if(eval(x->ch[i],mask))return 1;return 0;}
static void count(const Node*x,int*d,int*l){if(x->type==LEAF){(*d)++;return;}
  if(x->type==AND)*l+=x->nch-1;for(int i=0;i<x->nch;i++)count(x->ch[i],d,l);}
static int lmax(const Node*x){ /* worst-case |lambda|_1 */
  if(x->type==LEAF)return 1;int r=0;
  for(int i=0;i<x->nch;i++){int c=lmax(x->ch[i]);if(x->type==AND)r+=c;else if(c>r)r=c;}return r;}
static int zmax(const Node*x){ /* worst-case |z|_1 */
  if(x->type==LEAF)return 0;int r=0;
  for(int i=0;i<x->nch;i++){int c=zmax(x->ch[i]);if(x->type==OR)r+=c;else if(c>r)r=c;}
  return x->type==AND?r+(x->nch>1):r;}   /* conservative: 1 + max child */

typedef struct{int d,l,nslot,nfresh,gamma,Lam,zeta;int8_t*N;int*owner;}Lsss;
static void comp(Node*x,const int8_t*form,Lsss*L){
  int l=L->l;
  if(x->type==LEAF){x->slot=L->nslot;memcpy(L->N+(size_t)x->slot*l,form,l);L->owner[x->slot]=x->party;L->nslot++;return;}
  if(x->type==OR){for(int i=0;i<x->nch;i++)comp(x->ch[i],form,L);return;}
  int a=x->nch;x->fc=calloc(a,sizeof(int));
  for(int i=0;i<a-1;i++)x->fc[i]=L->nfresh++;
  int8_t*f=calloc(l,1);
  for(int i=0;i<a-1;i++){memset(f,0,l);f[x->fc[i]]=1;comp(x->ch[i],f,L);}
  memcpy(f,form,l);for(int i=0;i<a-1;i++)f[x->fc[i]]-=1;comp(x->ch[a-1],f,L);free(f);}
static void build(Node*F,Lsss*L){
  int d=0,l=1;count(F,&d,&l);L->d=d;L->l=l;L->nslot=0;L->nfresh=1;
  L->N=calloc((size_t)d*l,1);L->owner=malloc(d*sizeof(int));
  int8_t*f=calloc(l,1);f[0]=1;comp(F,f,L);free(f);
  L->gamma=0;for(int u=0;u<d;u++){int s=0;for(int j=0;j<l;j++)s+=abs(L->N[(size_t)u*l+j]);if(s>L->gamma)L->gamma=s;}
  L->Lam=lmax(F);L->zeta=zmax(F);}
static void select_(const Node*x,unsigned mask,int*lam){ /* canonical reconstruction vector */
  if(x->type==LEAF){lam[x->slot]=1;return;}
  if(x->type==AND){for(int i=0;i<x->nch;i++)select_(x->ch[i],mask,lam);return;}
  for(int i=0;i<x->nch;i++)if(eval(x->ch[i],mask)){select_(x->ch[i],mask,lam);return;}}
static void sweep(const Node*x,unsigned mask,int*z){ /* sweeping vector for T not in Gamma */
  if(x->type==LEAF)return;
  if(x->type==OR){for(int i=0;i<x->nch;i++)sweep(x->ch[i],mask,z);return;}
  int i=0;while(eval(x->ch[i],mask))i++;           /* first child false on T */
  if(i<x->nch-1)z[x->fc[i]]=1;
  sweep(x->ch[i],mask,z);}

/* ------------------------------------------------------------ commitment */
typedef struct{int lam_s,m,k,qbits;u64 By,Bop;int gamma,Lam,zeta;u64*A,*b;}PP;
static u64*yr; /* scratch */
static void com(const PP*p,u64 x,const i64*y,u64*out){
  int m=p->m,k=p->k;for(int j=0;j<m;j++)yr[j]=red(y[j]);
  for(int i=0;i<k;i++){u128 acc=0;const u64*row=p->A+(size_t)i*m;
    for(int j=0;j<m;j++){acc+=(u128)row[j]*yr[j];if((j&7)==7)acc%=Q;}out[i]=(u64)(acc%Q);}
  u128 acc=0;for(int j=0;j<m;j++){acc+=(u128)p->b[j]*yr[j];if((j&7)==7)acc%=Q;}
  out[k]=addmod((u64)(acc%Q),x%Q);}
static void setup(PP*p,const Lsss*L,int lam_s,int qbits,int m,int k){
  p->lam_s=lam_s;p->m=m;p->k=k;p->qbits=qbits;p->gamma=L->gamma;p->Lam=L->Lam;p->zeta=L->zeta;
  Q=next_prime(1ULL<<(qbits-1));
  p->By=(u64)L->zeta*m<<lam_s;if(p->By<1)p->By=1; /* paper assumes By>=1 (zeta=0 for 1-of-n) */p->Bop=(u64)L->gamma*p->By;
  p->A=malloc((size_t)k*m*8);p->b=malloc((size_t)m*8);
  for(size_t i=0;i<(size_t)k*m;i++)p->A[i]=rnd_below(Q);for(int j=0;j<m;j++)p->b[j]=rnd_below(Q);
  yr=realloc(yr,(size_t)m*8);}

typedef struct{u64*v,*D,*s;i64*Y,*W;}Shr;
static Shr share(const PP*p,const Lsss*L,u64 secret){
  int l=L->l,d=L->d,m=p->m,k=p->k;Shr S;
  S.v=malloc(l*8);S.Y=malloc((size_t)l*m*8);S.D=malloc((size_t)l*(k+1)*8);S.s=malloc(d*8);S.W=calloc((size_t)d*m,8);
  S.v[0]=secret;for(int j=1;j<l;j++)S.v[j]=rnd_below(Q);
  for(int t=0;t<m;t++)S.Y[t]=(i64)rnd_below(3)-1;
  for(int j=1;j<l;j++)for(int t=0;t<m;t++)S.Y[(size_t)j*m+t]=(i64)rnd_below(2*p->By+1)-(i64)p->By;
  for(int j=0;j<l;j++)com(p,S.v[j],S.Y+(size_t)j*m,S.D+(size_t)j*(k+1));
  for(int u=0;u<d;u++){u64 s=0;for(int j=0;j<l;j++){int8_t c=L->N[(size_t)u*l+j];if(!c)continue;
      s=addmod(s,mulmod(red(c),S.v[j]));for(int t=0;t<m;t++)S.W[(size_t)u*m+t]+=(i64)c*S.Y[(size_t)j*m+t];}S.s[u]=s;}
  return S;}
static void slotcom(const PP*p,const Lsss*L,const u64*D,int u,u64*out){
  int l=L->l,k=p->k;memset(out,0,(k+1)*8);
  for(int j=0;j<l;j++){int8_t c=L->N[(size_t)u*l+j];if(!c)continue;
    for(int i=0;i<=k;i++)out[i]=addmod(out[i],mulmod(red(c),D[(size_t)j*(k+1)+i]));}}
static int inorm_le(const i64*w,int m,u64 B){for(int t=0;t<m;t++){u64 a=w[t]<0?(u64)(-w[t]):(u64)w[t];if(a>B)return 0;}return 1;}
static int verify(const PP*p,const Lsss*L,const u64*D,int u,u64 s,const i64*w){
  u64 C[p->k+1],E[p->k+1];slotcom(p,L,D,u,C);
  if(!inorm_le(w,p->m,p->Bop))return 0;com(p,s,w,E);return memcmp(C,E,(p->k+1)*8)==0;}
/* returns 1 and fills *s_out on success */
static int reconstruct(const PP*p,const Lsss*L,const Node*F,const u64*D,unsigned mask,const u64*s,const i64*W,u64*s_out){
  int d=L->d,m=p->m,k=p->k;int*lam=calloc(d,sizeof(int));select_(F,mask,lam);
  u64 sp=0;i64*wr=calloc(m,8);int ok=1;
  for(int u=0;u<d&&ok;u++)if(lam[u]){if(!verify(p,L,D,u,s[u],W+(size_t)u*m))ok=0;
    sp=addmod(sp,s[u]);for(int t=0;t<m;t++)wr[t]+=W[(size_t)u*m+t];}
  if(ok&&inorm_le(wr,m,(u64)p->Lam*p->Bop)){u64 E[k+1];com(p,sp,wr,E);ok=!memcmp(E,D,(k+1)*8);}else ok=0;
  if(ok)*s_out=sp;free(lam);free(wr);return ok;}

/* ------------------------------------------------------------ SIS estimate (heuristic!) */
static double log2delta(int b){double B=b;return log2(pow(M_PI*B,1.0/B)*B/(2*M_PI*M_E))/(2*(B-1));}
/* smallest BKZ block size whose lattice-reduction output (best sub-dimension) is <= beta.
 * 0 = trivial (beta>=q), -1 = beyond b=2000 */
static int sis_block(double lq,int k,int m,double lbeta){
  if(lbeta>=lq)return 0;
  for(int b=50;b<=2000;b++){double ld=log2delta(b),dd=sqrt(k*lq/ld);if(dd>m)dd=m;if(dd<k+1)dd=k+1;
    if(dd*ld+k*lq/dd<=lbeta)return b;}
  return -1;}
static void report_params(int lam_s,double lq,int k,int m,double lBy,double zeta,double gamma,double Lam,double dl,double lBeta,int mode_log){
  (void)dl;(void)mode_log;
  double k1l=m*log2(3.0),k1r=(k+1)*ceil(lq)+2.0*lam_s;
  printf("  K1 hiding   : m*log2(3)=%.1f >= (k+1)ceil(lg q)+2*lam_s=%.1f   [%s]\n",k1l,k1r,k1l>=k1r?"ok":"FAIL");
  printf("  K2 flooding : log2 By = %.2f (By = zeta*m*2^lam_s)\n",lBy);
  printf("  K3 binding  : log2 beta_con = %.2f, log2 q = %.2f   [%s]\n",lBeta,lq,lBeta<lq?"beta<q ok":"FAIL beta>=q");
  int b=sis_block(lq,k,m,lBeta);
  if(b==0)printf("  SIS estimate: trivial (beta>=q)\n");
  else if(b<0)printf("  SIS estimate: needs BKZ block >2000 (very hard)\n");
  else printf("  SIS estimate: BKZ block ~%d  => ~2^%.0f classical / 2^%.0f quantum (core-SVP, crude; confirm with lattice-estimator)\n",b,0.292*b,0.265*b);
  (void)zeta;(void)gamma;(void)Lam;}

/* ------------------------------------------------------------ validation */
static int fails=0,checks=0;
#define CHECK(c,...) do{checks++;if(!(c)){fails++;printf("  FAIL: ");printf(__VA_ARGS__);printf("\n");}}while(0)

static void validate_policy(const char*name,Node*F,int n){
  Lsss L;build(F,&L);
  printf("[%s] n=%d d=%d l=%d gamma=%d Lambda<=%d zeta<=%d\n",name,n,L.d,L.l,L.gamma,L.Lam,L.zeta);
  PP p;setup(&p,&L,8,31,128,4);
  u64 secret=rnd_below(Q);Shr S=share(&p,&L,secret);
  int l=L.l,d=L.d,m=p.m,k=p.k;int nauth=0,nunauth=0;
  /* (b) honest slots verify */
  for(int u=0;u<d;u++)CHECK(verify(&p,&L,S.D,u,S.s[u],S.W+(size_t)u*m),"honest slot %d rejected",u);
  /* entries in {0,+-1} */
  for(int i=0;i<d*l;i++)CHECK(abs(L.N[i])<=1,"entry out of range");
  for(unsigned mask=0;mask<(1u<<n);mask++){
    if(eval(F,mask)){ nauth++;
      int*lam=calloc(d,sizeof(int));select_(F,mask,lam);int l1=0;
      for(int u=0;u<d;u++){if(lam[u]){CHECK(mask>>L.owner[u]&1,"S2 support outside set");l1+=lam[u];}}
      for(int j=0;j<l;j++){int sum=0;for(int u=0;u<d;u++)sum+=lam[u]*L.N[(size_t)u*l+j];CHECK(sum==(j==0),"S2 sum j=%d mask=%u",j,mask);}
      CHECK(l1<=L.Lam,"S2 norm");
      u64 got=0;int ok=reconstruct(&p,&L,F,S.D,mask,S.s,S.W,&got);
      CHECK(ok&&got==secret,"reconstruct failed mask=%u",mask);
      free(lam);
    } else { nunauth++;
      int*z=calloc(l,sizeof(int));sweep(F,mask,z);int zn=0;for(int j=1;j<l;j++)zn+=z[j];
      CHECK(z[0]==0&&zn<=L.zeta,"S3 norm");
      for(int u=0;u<d;u++)if(mask>>L.owner[u]&1){int sum=L.N[(size_t)u*l];for(int j=1;j<l;j++)sum+=L.N[(size_t)u*l+j]*z[j];CHECK(sum==0,"S3 violated slot %d mask=%u",u,mask);}
      /* (e) privacy shift identities */
      u64*rt=malloc(l*8);i64*yt=malloc((size_t)l*m*8);u64 sm=secret%Q;
      for(int j=1;j<l;j++){rt[j]=submod(S.v[j],mulmod(sm,(u64)z[j]));for(int t=0;t<m;t++)yt[(size_t)j*m+t]=S.Y[(size_t)j*m+t]-(i64)z[j]*S.Y[t];}
      for(int u=0;u<d;u++)if(mask>>L.owner[u]&1){u64 s=0;i64*w=calloc(m,8);
        for(int j=1;j<l;j++){int8_t c=L.N[(size_t)u*l+j];if(!c)continue;s=addmod(s,mulmod(red(c),rt[j]));for(int t=0;t<m;t++)w[t]+=(i64)c*yt[(size_t)j*m+t];}
        CHECK(s==S.s[u],"shift (i) slot %d",u);CHECK(!memcmp(w,S.W+(size_t)u*m,m*8),"shift (ii) slot %d",u);free(w);}
      for(int j=1;j<l;j++){u64 Dt[k+1];com(&p,rt[j],yt+(size_t)j*m,Dt);
        for(int i=0;i<=k;i++)Dt[i]=addmod(Dt[i],mulmod((u64)z[j],S.D[i]));
        CHECK(!memcmp(Dt,S.D+(size_t)j*(k+1),(k+1)*8),"shift (iii) D_%d mask=%u",j,mask);}
      free(rt);free(yt);free(z);}
  }
  printf("   authorized sets checked: %d, unauthorized: %d\n",nauth,nunauth);
  /* (d) attacks */
  int u0=d/2;i64*w=malloc(m*8);memcpy(w,S.W+(size_t)u0*m,m*8);
  CHECK(!verify(&p,&L,S.D,u0,addmod(S.s[u0],1),w),"tampered share accepted");
  w[0]+=1;CHECK(!verify(&p,&L,S.D,u0,S.s[u0],w),"tampered randomness accepted");
  memcpy(w,S.W+(size_t)u0*m,m*8);w[0]+=(i64)Q;
  CHECK(!verify(&p,&L,S.D,u0,S.s[u0],w),"non-short opening (w+q) accepted (bound check broken)");
  { /* same commitment value but not short: demonstrates why bound check is essential */
    u64 C1[k+1],C2[k+1];com(&p,S.s[u0],S.W+(size_t)u0*m,C1);com(&p,S.s[u0],w,C2);
    CHECK(!memcmp(C1,C2,(k+1)*8),"w+q should give same commitment mod q"); }
  { int acc=0;i64*z0=calloc(m,8);for(int u=0;u<d;u++)acc+=verify(&p,&L,S.D,u,0,z0);
    CHECK(acc==0,"zero-share attack: %d slots accepted",acc);free(z0);}
  { unsigned mask=0;for(unsigned mk=0;mk<(1u<<n);mk++)if(eval(F,mk)){mask=mk;break;}
    i64*W2=malloc((size_t)d*m*8);memcpy(W2,S.W,(size_t)d*m*8);u64*s2=malloc(d*8);memcpy(s2,S.s,d*8);
    int*lam=calloc(d,sizeof(int));select_(F,mask,lam);int uu=0;while(!lam[uu])uu++;s2[uu]=addmod(s2[uu],1);
    u64 got;CHECK(!reconstruct(&p,&L,F,S.D,mask,s2,W2,&got),"reconstruct accepted corrupted slot");free(W2);free(s2);free(lam);}
  printf("   attacks (tampered share/randomness, non-short opening, zero-share, corrupted reconstruction) tested\n");
  free(w);
}

static int cmd_validate(void){
  seed_rng(12345);
  validate_policy("2-of-3 DNF",threshold_dnf(2,3),3);
  validate_policy("3-of-5 DNF",threshold_dnf(3,5),5);
  validate_policy("1-of-4 DNF",threshold_dnf(1,4),4);
  /* mixed formula with repeated parties: (P0&P1) | (P0&(P2 | (P1&P3))) | (P2&P3&P4) */
  Node*F=gate(OR,3,gate(AND,2,leaf(0),leaf(1)),
                   gate(AND,2,leaf(0),gate(OR,2,leaf(2),gate(AND,2,leaf(1),leaf(3)))),
                   gate(AND,3,leaf(2),leaf(3),leaf(4)));
  validate_policy("mixed (repeated parties)",F,5);
  printf("\n%d checks, %d failures\n",checks,fails);
  puts(fails?"VALIDATION FAILED":"ALL VALIDATION CHECKS PASSED");return fails!=0;}

/* ------------------------------------------------------------ bench / plan */
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+1e-9*t.tv_nsec;}
static double binom(int n,int k){double r=1;for(int i=1;i<=k;i++)r=r*(n-k+i)/i;return r;}

static void cmd_plan(int t,int n,int lam_s,double qbits,int m){
  double C=binom(n,t);double l=1+(t-1)*C,d=t*C,gam=t,Lam=t,zeta=C;
  double lBy=log2(zeta*m)+lam_s,lBop=lBy+log2(gam),lBeta=1+log2(Lam)+lBop+0.5*log2(m);
  int k=(int)floor((m*log2(3.0)-2.0*lam_s)/ceil(qbits))-1;
  printf("PLAN %d-of-%d (minimal-set DNF): slots d=%.0f, coords l=%.0f, gamma=Lambda=%d, zeta=%.0f, slots/party=%.0f\n",t,n,d,l,t,zeta,binom(n-1,t-1));
  printf("  lam_s=%d m=%d q~2^%.0f; largest k allowed by K1: %d\n",lam_s,m,qbits,k);
  if(k<1){puts("  K1 cannot be met: increase m or lower q/lam_s");return;}
  report_params(lam_s,qbits,k,m,lBy,zeta,gam,Lam,0,lBeta,0);
  double lq=ceil(qbits);
  printf("  sizes: |D| = %.0f bits, key = %.0f bits, slot record = %.0f bits, per-party = %.0f bits\n",
     l*(k+1)*lq,(double)(k+1)*m*lq,lq+m*ceil(log2(2*gam*pow(2,lBy)+1)),binom(n-1,t-1)*(lq+m*ceil(lBop+1)));
  printf("  ops (Z_q mult-adds): Share coords=%.3g, slot randomness=%.3g, SlotCom/slot=%.3g, Verify/slot=%.3g, Reconstruct=%.3g\n",
     l*(k+1)*m,d*gam*m,gam*(k+1),(double)(k+1)*m+gam*(k+1),Lam*(k+1)*m);}

static void cmd_bench(int t,int n,int lam_s,int qbits,int m,int k){
  seed_rng(777);Node*F=threshold_dnf(t,n);Lsss L;build(F,&L);PP p;setup(&p,&L,lam_s,qbits,m,k);
  double lBy=log2((double)p.By),lBeta=1+log2(L.Lam)+log2((double)p.Bop)+0.5*log2(m);
  printf("BENCH %d-of-%d: d=%d l=%d gamma=%d Lambda=%d zeta=%d  q=%llu (%d bits) m=%d k=%d lam_s=%d\n",t,n,L.d,L.l,L.gamma,L.Lam,L.zeta,(unsigned long long)Q,qbits,m,k,lam_s);
  if(lBy>56){puts("  By too large for int64 arithmetic: lower lam_s/m");return;}
  report_params(lam_s,log2((double)Q),k,m,lBy,L.zeta,L.gamma,L.Lam,0,lBeta,0);
  double t0=now();Shr S=share(&p,&L,rnd_below(Q));double t1=now();
  u64*Cs=malloc((size_t)(k+1)*8);double ts=now();for(int u=0;u<L.d;u++)slotcom(&p,&L,S.D,u,Cs);double te=now();
  double tv=now();int ok=1;for(int u=0;u<L.d;u++)ok&=verify(&p,&L,S.D,u,S.s[u],S.W+(size_t)u*m);double tw=now();
  unsigned mask=(1u<<t)-1;u64 got=0;int R=10;double tr=now();for(int i=0;i<R;i++)ok&=reconstruct(&p,&L,F,S.D,mask,S.s,S.W,&got);double tq=now();
  printf("  all honest slots verify & reconstruct ok: %s\n",ok&&got==S.v[0]?"yes":"NO");
  printf("  time: Share %.3f ms | SlotCom %.4f ms/slot | VerifyShare %.4f ms/slot (incl. SlotCom) | Reconstruct+verify %.3f ms\n",
     1e3*(t1-t0),1e3*(te-ts)/L.d,1e3*(tw-tv)/L.d,1e3*(tq-tr)/R);
  double lq=ceil(log2((double)Q));
  printf("  sizes: |D| = %.0f bytes, key = %.0f bytes, slot record = %.0f bytes (32-bit-aligned bit counts: %.0f bits)\n",
     L.l*(k+1)*lq/8,(double)(k+1)*m*lq/8,(lq+m*ceil(log2(2.0*L.gamma*p.By+1)))/8,lq+m*ceil(log2(2.0*L.gamma*p.By+1)));
  printf("  per party: %.0f slots, %.1f KiB\n",binom(n-1,t-1),binom(n-1,t-1)*(lq+m*ceil(log2(2.0*L.gamma*p.By+1)))/8/1024);
}

int main(int argc,char**argv){
  if(argc>=2&&!strcmp(argv[1],"validate"))return cmd_validate();
  if(argc>=8&&!strcmp(argv[1],"bench")){cmd_bench(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]),atoi(argv[5]),atoi(argv[6]),atoi(argv[7]));return 0;}
  if(argc>=7&&!strcmp(argv[1],"plan")){cmd_plan(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]),atof(argv[5]),atoi(argv[6]));return 0;}
  fprintf(stderr,"usage: %s validate | bench t n lam_s qbits m k | plan t n lam_s qbits m\n",argv[0]);return 1;}
