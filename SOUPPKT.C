#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <io.h>
#include <fcntl.h>
#include <sys\types.h>
#include <sys\stat.h>
#include <process.h>

#define BLKSIZE 1024
#define FALSE 0
#define TRUE (!FALSE)

//global error flag for *.pkt write
int err=0;

//global variables read from soupbox.cfg for souppkt & pktsoup conversion
char email[40];           //soup area tagname to strip from/add to e-mail
int nb=0;                 //# of binaries hierarchies & special handler progs
char bin[10][80];         //root name of binary groups to send to decode.cmd
char decoder[10][40];     //names of programs to store or decode binaries
int nd=0;                 //# of defined ftn destinations/domain names
char domain[40][80];      //domain to put in "from:user@domain" for pkt2soup.c
struct FADDR
 {short zone,net,node,point;}
 org, dest[40];            //fido-style *.pkt source & destination address
unsigned long split=12345; //point to split long inbound soup->ftn messages
char reply[80],tz[40];     //path to outbound ftn packet and name of timezone
int ne=0;                  //number of e-mail attach downlinks
char encoder[10][40],      //program to encode e-mail attach packets
     eheader[10][40],      //header to prepend to encoded e-mail
     epacket[10][60];      //files to send as encoded e-mail

int nr=0;                  //number of user replace/replaceall/alias addresses
char addr0[40][50],
     addr1[40][50],
     reptype[40];
#define ALIAS 1
#define REPLACE 2
#define REPLACEALL 3

//call write() and remember error codes
int wwrite(int file,char *blk,int len)
{
 int rc;
 rc=write(file,blk,len);
 if (rc<0)
   err=rc;
 return rc;
}

//read soupbox.cfg configuration file - note some of these values are unused
//store result in global variables - return TRUE if successful, else FALSE
int initialize(char *file)
{
 FILE *in;
 static char line[128],tag[40],val1[80],val2[80],val3[80];  //one line of soupbox.cfg file

 in=fopen(file,"r");
 if (!in)
  {printf("error - unable to open soupbox.cfg");
   return FALSE;}

 while (!feof(in))
   {
    line[0]=tag[0]=val1[0]=val2[0]=val3[0]=0;
    fgets(line,sizeof(line),in);
    sscanf(line,"%s %s %s %s",tag,val1,val2,val3);
    if (!stricmp(tag,"Origin"))
        sscanf(val1,"%d:%d/%d.%d",&org.zone,&org.net,&org.node,&org.point);
    if (!stricmp(tag,"Domain"))
     {
        sscanf(val1,"%d:%d/%d.%d",&dest[nd].zone,&dest[nd].net,&dest[nd].node,&dest[nd].point);
        strcpy(domain[nd],val2);
        nd++;
      }
    if (!stricmp(tag,"e-mail"))
         strcpy(email,val1);
    if (!stricmp(tag,"Split"))
         sscanf(val1,"%ld",&split);     //#bytes at which to split long msgs
    if (!stricmp(tag,"Encode"))
     {
        strcpy(encoder[ne],val1);       //name of encoder program
        strcpy(eheader[ne],val2);       //header for e-mail attach
        strcpy(epacket[ne],val3);       //packets to send via e-mail attach
        ne++;
      }
    if (!stricmp(tag,"Decode"))
     {
        strcpy(decoder[nb],val1);
        strcpy(bin[nb],val2);
        nb++;
      }
    if (!stricmp(tag,"Alias"))
     {
        strcpy(addr0[nr],val1);       //address on BBS for this user
        strcpy(addr1[nr],val2);       //address to use on internet
        reptype[nr]=ALIAS;
        nr++;
      }
    if (!stricmp(tag,"Replace"))
     {
        strcpy(addr0[nr],val1);       //address on BBS for this user
        strcpy(addr1[nr],val2);       //address to use on internet
        reptype[nr]=REPLACE;
        nr++;
      }
    if (!stricmp(tag,"ReplaceAll"))
     {
        strcpy(addr0[nr],val1);       //address on BBS for this user
        strcpy(addr1[nr],val2);       //address to use on internet
        reptype[nr]=REPLACEALL;
        nr++;
      }
    if (!stricmp(tag,"Reply"))
        strcpy(reply,val1);
    if (!stricmp(tag,"TimeZone"))
         strcpy(tz,val1);
   }
 fclose(in);

 if (!nd)
 {
   printf("error - no fido destination address & domain name in config file\n");
   return FALSE;
 }

 //TO DO: check config. values for validity
 return TRUE;
}

//souppkt.c-specific section

//this writes a fts-0048 (type 2+) fido packet header using org, dest[0] as
//node number, no packet passwords

int pkthdr(int file)
{
  int i;
  //org/dest[0] node
  write(file,&org.node,2);
  write(file,&dest[0].node,2);
  //use dummy values for date/time - Aug 1997
  write(file,"\xcd\x07\x07\x00\x0f\x00\x00\x00\x00\x00\x00\x00",12);
  //bps=0, pkt type=2
  write(file,"\x00\x00\x02\x00",4);
  //org/dest[0] net
  i=org.net;
//if (org.point) i=-1;        //originating net=-1 if point
  write(file,&i,2);
  write(file,&dest[0].net,2);
  //prod code=fido
  write(file,"\x00\x01",2);
  //no packet password
  write(file,"\x00\x00\x00\x00\x00\x00\x00\x00",8);
  //org/dest[0] zone
  write(file,&org.zone,2);
  write(file,&dest[0].zone,2);
  //remainder is type2+ hdr data for ftsc48 4D/point support
  write(file,&org.net,2);       //aux net
  i=256;write(file,&i,2);       //2nd capability word
  i=176;write(file,&i,2);       //product/revision code
  i=1;write(file,&i,2);         //capability word
  //org/dest[0] zone
  write(file,&org.zone,2);
  write(file,&dest[0].zone,2);
  //org/dest[0] point
  write(file,&org.point,2);
  write(file,&dest[0].point,2);
  write(file,"XPKT",4);
}

//tofield() - this changes Internet "to:" field to BBS username & domain #
unsigned tofield(char *to,char *s,int maxlen)
{
    int i,st=0,end=0;
    int dom;               //pointer to BBS in list of our domains

    //extract first user@domain address from Internet to: field
    //remove trailing (screen name) or > from address
    while (s[end] && s[end]!='(' && s[end]!='>') end++;
    //remove scrname if scrname <addr@domain> format
    while (s[st] && s[st]!='<') st++;
    if (s[st]==0)
    {
      st=0;               //remove leading punctuation
      while (s[st] && s[st]<'0') st++;
    }
    else st++;           //skip over < in address
    strcpy(to,s+st);
    to[end-st]=0;

    //replace forwarded outside Internet addresses with user@BBS addresses
    for (i=0;i<nr;i++)
      if (!stricmp(to,addr1[i]))
        strcpy(to,addr0[i]);

    //remove @domain for our addresses on inbound mail
    {
     int j,dd=0;
     dom=0;
     while (to[dd] && to[dd]!='@') dd++;     //get domain name
     if (to[dd]) dd++;
     if (to[dd])
      {
       for (i=0;i<nd;i++)
       {
         if (!stricmp(domain[i],to+dd))     //if inbound to one of ours
           {
            dom=i;                          //keep index into BBS domain list
            to[dd-1]=0;                     //remove domain name
            for (j=0;j<=dd-1;j++)
              if (to[j]=='.') to[j]=' ';    //change .'s to spaces
            break;
           }
        }
      }
    }
    to[maxlen]=0;
    return dom;                              //return index to our list of BBS domains
}

//this reads ASCII headers from inbound soup to get date/from/x-to/subj
unsigned gethdr(int msg,char date[],char from[],char to[],char subj[],char orgn[])
{
 unsigned char s[255],p;
 unsigned long posn;
 unsigned dom=0;              //domain # as determined from to: field of e-mail

 //remember original position
 posn=lseek(msg,0,SEEK_CUR);

 //read headers until empty line found
 do
 {
   s[0]='\n';

   //read a line of input
   read(msg,s,1);
   for (p=1;p<255 && s[p-1] != '\n';p++)
     read(msg,s+p,1);
   s[p]=0;
   if (p>1)
     s[p-1]=0;

   //keep date/from/x-to/subject if found
   //delete any leading spaces or unwanted info
   if (!memcmp(s,"Date:",5))
     {
       int p1;
       p=5;
       while (s[p] && (s[p]<'0' || s[p]>'9')) p++;
       //strip 19.. from beginning of 19xx year (not y2k compliant)
       if ((!memcmp(s+p+6," 19",3)) || (!memcmp(s+p+6," 20",3)))
          for (p1=p+7;s[p1];p1++) s[p1]=s[p1+2];
       if ((!memcmp(s+p+5," 19",3)) || (!memcmp(s+p+5," 20",3)))
          for (p1=p+6;s[p1];p1++) s[p1]=s[p1+2];
       s[p+19]=0;
       strcpy(date,s+p);
     }
   //strip screen names and leading spaces from From:
   if (!memcmp(s,"From:",5))
     {
        p=5;                 //remove trailing (screen name) or > from address
        while (s[p] && s[p]!='(' && s[p]!='>') p++;
        s[p]=0;
        p=5;                 //remove scrname if scrname <addr@domain> format
        while (s[p] && s[p]!='<') p++;
        if (s[p]==0)
        {
          p=5;               //remove leading punctuation
          while (s[p] && s[p]<'0') p++;
        }
        else p++;           //skip over < in address
        s[p+35]=0;
        strcpy(from,s+p);
      }
   //strip leading spaces from x-to and subject lines
   if (!memcmp(s,"X-To:",5))
      dom=tofield(to,s+5,35);
   if (!memcmp(s,"To:",3))
      dom=tofield(to,s+3,35);
   if (!memcmp(s,"X-Ftn-To:",9))
      dom=tofield(to,s+9,35);
   if (!memcmp(s,"Subject:",8))
     {p=8;
      while (s[p] && s[p]<'0') p++;
      s[71+p]=0;strcpy(subj,s+p);}
   if (!memcmp(s,"Organization:",13))
     {p=13;
      while (s[p] && s[p]<'0') p++;
      s[56+p]=0;strcpy(orgn,s+p);}
 }
 //quit on empty line or eof and restore original position
 while (s[0]!='\n');
 lseek(msg,posn,SEEK_SET);
 return dom;
}

//write message headers for one fido-style message
//this may be called more than once if a message is split due to length
void writehdr(int file,char *date,char *from,char *to,char *subj,char *area,unsigned dom,unsigned part)
{
  //write message header
  write(file,"\x02\x00",2);
  write(file,&org.node,2);
  write(file,&dest[dom].node,2);
  write(file,&org.net,2);
  write(file,&dest[dom].net,2);

  //attributes and cost
  if (!!stricmp(area,email))
    write(file,"\x00\x00\x00\x00",4); //public (echo) message
  else
    write(file,"\x01\x00\x00\x00",4); //private (netmail)

  //write date/to/from/subj
  write(file,date,strlen(date)+1);
  write(file,to,strlen(to)+1);
  write(file,from,strlen(from)+1);
  if (!part)
     write(file,subj,strlen(subj)+1);
  else
    {
     char s[80];             //insert segment # if a split/long msg
     s[0]='0'+part/10;
     s[1]='0'+part%10;
     s[2]=':';
     strcpy(s+3,subj);
     s[72]=0;
     write(file,s,strlen(s)+1);
    }

  //write area tag
  if (!!stricmp(area,email))
  {
    write(file,"AREA:",5);
    write(file,area,strlen(area));
    write(file,"\r",1);
  }
  //write FMPT/TOPT/INTL netmail kludges if needed in netmail
  else
  {
    char s[80];
    sprintf(s,"\001FMPT %d\r",org.point);
    if (org.point)
      write(file,s,strlen(s));
    sprintf(s,"\001TOPT %d\r",dest[dom].point);
    if (dest[dom].point)
      write(file,s,strlen(s));
    sprintf(s,"\001INTL %d:%d/%d %d:%d/%d\r", org.zone, org.net, org.node,
            dest[dom].zone, dest[dom].net, dest[dom].node);
    if (org.zone!=1 || dest[dom].zone!=1)
      write(file,s,strlen(s));
  }
}

//write ftn message footer - origin, end markers
void writeftr(int file,char *area,char *orgn)
{
  //write fido origin line and control info
  if (!!stricmp(area,email))
  {
     char addr[40];

     //write tearline and origin line
     write(file,"\r\r---\r * Origin: ",17);
     write(file,orgn,strlen(orgn));
     sprintf(addr," (%d:%d/%d.%d)\r",org.zone,org.net,org.node,org.point);
     write(file,addr,strlen(addr));

     //write echomail SEEN-BY and PATH:
     sprintf(addr,"SEEN-BY: %d/%d\r",org.net,org.node);
     write(file,addr,strlen(addr));
     sprintf(addr,"\001PATH: %d/%d\r",org.net,org.node);
     write(file,addr,strlen(addr));
  }
  //write end marker
  write(file,"",1);
}

//convert one individual message to include in existing *.pkt file
//assume packet header has already been written
int cvtm2pkt(int file,int msg,char *area)
{
  unsigned i,j;
  unsigned char c,mlen[4];
  unsigned long len,pos,segpos;
  static unsigned char date[20],from[40],to[40],subj[80],orgn[80];
  int rc;
  unsigned dom;         //index into BBS domain list for inbound e-mail
  unsigned part=0;      //segment # if splitting long message

  rc=read(msg,&mlen,4);     //get length of message body
  if (rc<=0)
    return 0;
  len=0;
  for (i=0;i<4;i++)
    len= (len << 8L)+(unsigned long) mlen[i];

  //defaults-gethdr will replace these with actual message info if present
  strcpy(date,"01 Jan 97  00:00:00");
  strcpy(from,area);
  strcpy(to,"All");
  strcpy(subj,"stuff");
  strcpy(orgn,"none");

  //get header info from message
  dom=gethdr(msg,date,from,to,subj,orgn);
  if (!!stricmp(area,email))
    dom=0;                      //send all news to first (default) BBS domain

  if (len>split) part=1;
  writehdr(file,date,from,to,subj,area,dom,part); //write header for one ftn message

  //copy message body
  rc=1;
  segpos=0;                  //position in this segment of split/long message

  for (pos=0;pos<len && rc>0;)
  {
    unsigned long blksize=len-pos;
    unsigned char c[BLKSIZE];
    int i;
    if (blksize>BLKSIZE)
       blksize=BLKSIZE;
    if (segpos+blksize > split)
       blksize=split-segpos;
    rc=read(msg,c,(unsigned) blksize);
    for (i=0;i<blksize;i++)
      if (c[i]==10) c[i]=13; //convert lf to cr
    write(file,c,(unsigned) blksize);
    pos+=blksize;
    segpos+=blksize;
    if (segpos>=split && pos<len)    //if too long, insert a ftn split here
    {
      //copy remainder of current line
      char c=0;
      while (pos<len && c!=13 && rc>0)
        {
         rc=read(msg,&c,1);
         if (c==10) c=13; //convert lf to cr
         write(file,&c,1);
         pos++;
        }
      //create split (msg footer then header of next segment)
      //TO DO: indicate split in ftn kludge lines
      writeftr(file,area,orgn);
      part++;                    //increment msg part# in subject line
      writehdr(file,date,from,to,subj,area,dom,part);
      segpos=0;
    }
  }

  writeftr(file,area,orgn);         //write ftn footer - origin: and end markers
  return 1;
}

void main(void)
{
 static unsigned char fname[40],area[40],type[20];
 int i;
 FILE *areas;

 err=0;
 if (!initialize("soupbox.cfg"))
   return;

 areas=fopen("areas","rb");
 if (!areas)
   return;

 while (!feof(areas))
 {
  int in,out;
  static char pkt[40];
  fname[0]=area[0]=type[0]=0;
  if (fscanf(areas,"%s\t%s\t%s\n",fname,area,type)>0)
  {
     printf("file %s area %s type %s",fname,area,type);
     strcpy(pkt,fname);
     strcat(fname,".msg");
     strcat(pkt,".pkt");
     for (i=0;i<nb;i++)
      if (!memicmp(area,bin[i],strlen(bin[i])))  //if binary group, give msg to decoder
      {
       char s[80];
       sprintf(s,"%s %s %s",decoder[i],fname,area);
       system(s);
      }
     in=open(fname,O_RDONLY|O_BINARY);    //if msg still exists, convert to .pkt
     //check to see if output .pkt file already exists
     out=open(pkt,O_RDONLY|O_BINARY);
     if (out>0)
     {
       err=1;close(out);
       printf("\nerror creating %s - file already exists\n",pkt);
       exit(1);
     }
     else if (in>0)
     {
        out=open(pkt,O_WRONLY|O_BINARY|O_CREAT|O_TRUNC,S_IREAD|S_IWRITE);
        pkthdr(out);
        while (cvtm2pkt(out,in,area)) printf(".");
        printf("\n");
        write(out,"\0",2);
        close(out);
     }
     close(in);
     if (!err)
       remove(fname);
  }
 }
 fclose(areas);
 if (!err)
   remove("areas");
 else
   printf("\ndisk write error during soup/pkt conversion\n");
}
