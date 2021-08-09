// By Aris Anagnostakis (arian@uoi.gr)
// Created: Jan 8th 2021 
// THIS IS THE FULL NODE of the IoT Blockchain v0.1
// It contains all the ingredients for building a prime IoT Blockchain 
// Tested on Arduino Nano33 IoT. WiFiNINA firmware 1.4.0 and Library 1.7.0
// Last updated: Jan 19th 2021
// This contains code for: 1. connection (http server & client over wifi, 2. encryption, 3. hashing
// Integrating Access Point, Server, Client, Blockchain, Hash and RSA code. 
// Kudos to https://stackoverflow.com/users/6125661/telkepalli-venkat-karthik for experimental RSA
// Modified accordingly for maximum capacity via "long unsigned" keys, bounded and tested in range
// Implementing https://simple.wikipedia.org/wiki/RSA_algorithm
//This is a proof of the concept that autonomous IoT blockchains can be build based on minimal HW.
// 
//
//--------------------------------------------------------------------------------------------------
//Description: 
// The idea is to immune local transactions taking place in one device (i.e. the opening of a door), 
// by creating "neighborhoods of transaction witnesses".
//
// When a local event rises, it is stored in the local chain and it is transmitted to other arduinos
// in range to store in their chains. 
//
// Due to memory limitations, each arduino device maintains only the latest N transactions.
// This can be resolved by adding peers with "unlimited" capacity in the range of all neighbours.
// This is a model prototype part of my Thesis, delivered without any warranty. 
//   
//
//--------------------------------------------------------------------------------------------------
//Operation: 
//
// Peer, totally autonomus IoT Blokchain architecture based solely on arduino devices.
// This sketch transforms every arduino to a full node of this prototype IoT Blockchain, 
// operating without the need of any third party or other devices.
//
// Each Arduino stores locally part of the Blockchain.
// The Blockchain consists of consecutive EUI (Event Unique Identifier) objects, 
// representing primitive transactions such as turning on a light, or unlocking a door.
//
// Each arduino is initialised in setup(),and a pair of Public-Private keys is assigned to it.
// It then becomes Access Point waiting for incomming EUIs.
//
//FLOW description:
// 1. On Setup() create the local Public Private keys pair. 
// 2. Become access point and http server and wait for incoming packages, 
//    if any, verify it (and store it on the local chain).
// 3. If a local event rises in the meanwhile, (e.g. if a switch is pressed, a door is unlocked etc.) 
//    then create a new EUI and store it to the local chain, became client and transmit it to neigbours
//
//--------------------------------------------------------------------------------------------------
//Notes:
// ALL nodes in the IoT Blockchain network are running the same code.
// For test purposes: we assign ssid and password manually on each node. 
// Ad-hoc siblings scan not implemented here.
// We also adapt the HAT variable to set the frequency of local events occurence. 
// 
//
//--------------------------------------------------------------------------------------------------
//Known Bugs:
// RSA is only tested with up to 14-bit keys due to long unsigned length limit
// millis() to be eliminated for operational uptime to exceed unsigned long millis


//******************************************************************************************************
//**********************************LIBRARIES
//******************************************************************************************************
#include <SPI.h>
#include <WiFiNINA.h>
#include <WiFiUdp.h>
#include <Arduino.h> //needed for Enc/Dec
#include "sha256.h" //needed for hashing, to connect events in the Local Chain

//******************************************************************************************************
//**********************************GLOBAL VARIABLES
//******************************************************************************************************
//Network configuration: every device is an access point by itself. It runs a local server on 192.1168.4.1
//When another device connects to this it as a client, it aquires an IP: 192.168.4.x via DHCP
//When a LocalEvent rises, the node connects to all its siblings 
//Initially "OtherNode" is a single arduino access point executing this same code.
const char ThisNodeSsid[]="IoT_BlockchainNode_2"; //**TO be swapped mannually on each installation during development. For building Network an array of SSIDs updated regularly may be build
const char OtherNodeSsid[]="IoT_BlockchainNode_1";
const char ThisNodePass[]="12345678";
const char OtherNodePass[]="12345678";
bool IamServer=false; //if false i am client
void printWifiStatus();
unsigned long TimesConnected=0;

//Blockchain objects
unsigned long const LocalChainMaxLength=10;
unsigned long EventData=0;
unsigned long LocalEventCounter=0;
unsigned long LastLocalEventMillis=0;
unsigned long LastEventCursor=0; //to become LastEventCursor=LocalEventcounter % LocalChainLength; for circular rewriting 
unsigned long LastExternalDeviceID=0;
byte HashLastExternal[32]={1};

struct EUI //Event Unique Identifier "object" used to store data defining a Transaction Event in the IoT Blockchain
{ unsigned long DeviceID; // 4 Bytes, For human interaction only; overlapped by PublicKey 
  unsigned long PublicKey;
  unsigned long Field;
  unsigned long LocalEventCounter;
  unsigned long EventData;
  unsigned long LastExternalDeviceID; //48 Bytes
  byte HashLastExternal[32];
  byte HashPrevInternal[32];
  byte HashLastInternal[32];
  unsigned long HashLastInternalSigned[32];
  };

EUI CurrentEUI;

const int union_size = sizeof(EUI); //Data can also be accessed as Bytes, usefull for transmitting the event
union EUI_Packet{
 EUI EventObject;
 byte byteArray[union_size]; 
};
EUI_Packet CurrentEUIPacket; // Create a variable EUI_Packet
EUI_Packet EUI_Packet_Buffer;// Create a buffer to read incoming event
EUI_Packet Blockchain[LocalChainMaxLength]; // This is the Blockchain of the Local Node

byte VerificationBuffer[32];


struct EncryptedWord{ //this is to encrypt/decrypt a single byte array
unsigned long EW_Object; 
};
const int unionWord_size = sizeof(EUI);//this is to encrypt/decrypt a single byte array

union EW_Packet{
  EncryptedWord Buffer;
  byte byteArray[unionWord_size]; 
};
EW_Packet CurrentEW_Packet;  //Encrypted Packet
EW_Packet CurrentDEW_Packet; //Decrypted Packet


//Hashing objects
const char hexMap[] PROGMEM = "0123456789abcdef";

//SERVER section
char ssid[] = "IoT_BlockchainNode_2";  // your network SSID (name) Now connect to the "other node" (IOT_BlockchainNode_1), 1 will be replaced by N if N IoT_BlockchainNodes are scanned and operate around
char pass[] = "12345678";              //SECRET_PASS;    // your network password (use for WPA, or use as key for WEP)
int keyIndex = 0;                      // your network key Index number (needed only for WEP)
int led =  LED_BUILTIN;
int status = WL_IDLE_STATUS;
WiFiServer server(80);
IPAddress myserver(192,168,4,1); //when i am on "server" mode, my IP is 192.168.4.1

//CLIENT section
WiFiClient client;
bool LocalEventOccurred; // On the light of Local Event

//Encryption variables - RSA  
//Each Node has a specific DevID serving as PUBLIC KEY.
//On setup (i.e. once in lifetime) a private key is generated. Parameter phi is utilised for chinese RSA algorithm implementation method to accelerate Enc/Dec
//For simplicity we do not read the DevID from the EPROM, but a Prime Long number is assigned to also be uesd as the PUBLICK KEY.Up to 14-bit has been tested.

const unsigned long DevID = 23167; // 18547;// *Has to be different in each device in the IoT chain. 
unsigned long Firstprime, Secondprime, Privatekey, Publickey;
unsigned long Field, phin, Enc, Dec;
bool Hasrun= false, FalseFound= false;
unsigned long Text = 12; //16384; //on > some number, error in enc/dec process (unsigned Long overflow)
unsigned long Iterations=0, Success=0, FirstFailure=0;
// unsigned long HAT = 167200, TotalHats=0; // once in HAT times a local event rises 
unsigned long HAT = 500, TotalHats=0; //second application HAT in milliseconds interval among local events


//Benchmarking 
unsigned long Tbegin, Tbegin2,Tbegin3,Tbegin4,Tbegin5,Tbegin6,Tbegin7,Tbegin8,Tbegin9,Tbegin10, Tcs, Tsc, Ttransmission, Treception, Tverify, Thash, Tsign, Tcopy, Tidle, Taddexternal;
unsigned long Aborts=0;
//******************************************************************************************************
//**********************************GLOBAL END
//******************************************************************************************************



//****************************************************************************************************************
//Communications  section start
//****************************************************************************************************************
//===========================================================================
void BlockchainClientOnce(){ //Run once on a Local event. Toggle from server to client
                             //Here all known Blockchain nodes are being notified of my new Local Event
Tbegin3=millis();
Serial.print("************************************Tbegin3 =");Serial.println(Tbegin3);

                             
  IamServer=false;
  int attempts=0, maxattempts=3;
  //stop previous client instance and disconnect from Wifi.
  client.flush();
  client.stop();
  WiFi.end();
  // WiFi.disconnect(); 
 
    Serial.begin(9600);
  //while (!Serial) {
  //; // wait for serial port to connect. Needed for native USB port only
  // }
  
  //Connect to the OtherNode
  memcpy(ssid, OtherNodeSsid, sizeof(ssid)); //make me client
  Serial.print("Running BlockchainClientOnce, current SSID:");Serial.println(ssid);
  memcpy(pass, OtherNodePass, sizeof(pass));
  Serial.print("current SSID:");Serial.println(ssid);
  Serial.print("current PASS:");Serial.println(pass);


  //********************Known Good Client
  //BLINK(2,500);//Benchmark
  Serial.println("Becoming Client");
  // check for the WiFi module:
  if (WiFi.status() == WL_NO_MODULE) {
    Serial.println("Communication with WiFi module failed!");
    // don't continue
    while (true);
  }

  String fv = WiFi.firmwareVersion();
  if (fv < WIFI_FIRMWARE_LATEST_VERSION) {
    Serial.println("Please upgrade the firmware");
  }

  // attempt to connect to Wifi network:
  while (status != WL_CONNECTED && attempts<maxattempts) {
    Serial.print("Attempting to connect to SSID: ");
    Serial.println(ssid);
    // Connect to WPA/WPA2 network. Change this line if using open or WEP network:
    status = WiFi.begin(ssid, pass);

    // wait a while for connection, higher in case of many neigbours:
    delay(100);//Benchmark 100
    attempts++;
  }
  
  if (attempts<maxattempts){
    Serial.println("Connected to OtherNode Wifi");
    printWifiStatus();

  Serial.println("\nStarting connection to http server...");
  // if you get a connection, report back via serial:
  if (client.connect(myserver, 80)) {
    Serial.print("Connected to http server ");Serial.print(myserver); Serial.print(", running on Node:"); Serial.println(ssid);
  
    //*********************************************************************
    //HERE my Event object (EventUniqueIdentifier EUI) is TRANSMITTED to the world 
    // Make a repeated HTTP request to KNOWN Server(s) (IoT_Blockchain_Node_1 for testing)
    //PpkiExecute();  
      Serial.print("Printing the last Blockchain object to the serial wifi connection with the Other node...b)");
Tbegin2=millis();
Serial.print("************************************Tbegin2 =");Serial.println(Tbegin2);

      for(int i=0; i < union_size; i++)
      {
        client.write(Blockchain[LastEventCursor].byteArray[i]);
        delay(1);
        Serial.print("Sending byte ");Serial.print(i); Serial.print(" with value: "); Serial.print(Blockchain[LastEventCursor].byteArray[i]);
      } 
Ttransmission=millis()-Tbegin2;
Serial.print("************************************Transmission =");Serial.println(Ttransmission);
      
      client.println();
      Serial.println();
      delay(500);//give time to the other side to process//Benchmark 1000
      Serial.print("Disconnecting form OtherNode: "); Serial.println(ssid);
      client.flush();
      client.stop();
      WiFi.end();
      //WiFi.disconnect(); 
   }
  }
  else{
      Aborts++;
      Serial.print("FAILED TO CONNECT TO ");Serial.print(ssid);Serial.print(" ABORTING after attempts:");Serial.println(attempts);
      Serial.print("Total Network Abotrts : ");Serial.print(Aborts);Serial.print(" out of Local events count: ");Serial.println(LocalEventCounter);
      client.println();
      Serial.println();
      //delay(1000);//give time to the other side to process//Benchmark
      Serial.print("Disconnecting form OtherNode: "); Serial.println(ssid);
      client.flush();
      client.stop();
      WiFi.end();
  }
Tsc=millis()-Tbegin3-Ttransmission;
Serial.print("************************************Tsc =");Serial.println(Tsc);
}


//===========================================================================
void BlockchainServerSetup(){ //Run once on each toggle from client to server
 
  Serial.begin(9600);
  //  while (!Serial) {
  //    ; // wait for serial port to connect. Needed for native USB port only
  //  }
  
  
  client.flush();//Stop client if running
  client.stop();
  WiFi.end();
  //WiFi.disconnect(); 
  
  //Swapping Hats, turning to Server
  if (IamServer==false){
  memcpy(ssid, ThisNodeSsid, sizeof(ssid)); //make me server
  //Serial.print("Becoming Server again, current SSID:");Serial.println(ssid);
  memcpy(pass, ThisNodePass, sizeof(pass));
  //pass=OtherNodePass;
  //Serial.print("current PASS:");Serial.println(pass);
  }

  Serial.println("Now I am becoming Access Point &  Web Server listening on port 80");

  pinMode(led, OUTPUT);      // set the LED pin mode

  // check for the WiFi module:
  if (WiFi.status() == WL_NO_MODULE) {
    Serial.println("Communication with WiFi module failed!");
    // don't continue
    while (true);
  }

  String fv = WiFi.firmwareVersion();
  if (fv < WIFI_FIRMWARE_LATEST_VERSION) {
    Serial.println("Please upgrade the firmware");
  }

  // by default the local IP address of will be 192.168.4.1
  // you can override it with the following:
  // WiFi.config(IPAddress(10, 0, 0, 1));

  // print the network name (SSID);
  Serial.print("Inside BlockchainServerSetup(), becoming Access Point and Server: "); Serial.println(ssid);

  // Create open network. Change this line if you want to create an WEP network:
  status = WiFi.beginAP(ssid, pass);
  if (status != WL_AP_LISTENING) {
    Serial.println("Creating access point failed");
    // don't continue
    while (true);
  }

  // wait 10 seconds for connection:
  delay(100);//Benchmark
  
  // start the web server on port 80
  server.begin();
  IamServer=true;

  // you're connected now, so print out the status
  printWifiStatus();
}


//===========================================================================
void BlockchainServerLoop(){ // I am Server by default. If after processing an incoming, if I get Internal Event, then run I BlockchainClientOnce(). I return here via the main loop() 

  if (IamServer==false){ //make me server again
      client.flush();
      client.stop();//Stop me from client if running
      WiFi.end();
      //WiFi.disconnect(); 
      BlockchainServerSetup();
  }
  IamServer=true;
  
  //Serial.println("I am Server Now, listening for incoming events");
//Tbegin9=millis();
//Serial.print("************************************Tbegin9 idle =");Serial.println(Tbegin9);


if (status != WiFi.status()) {
    // it has changed update the variable
    status = WiFi.status();

    if (status == WL_AP_CONNECTED) {
      // a device has connected to the AP
      Serial.println("Device connected to AP");
    } else {
      // a device has disconnected from the AP, and we are back in listening mode
      Serial.println("Device disconnected from AP");
    }
  }

  //WiFiClient listen 
  client = server.available();                               // listen for incoming clients
  if (client) {                                              // if I get a client,
    TimesConnected++;                                        // Debugging counter
    Serial.print("New client, Connection No: ");             // print a message out the serial port
    Serial.println(TimesConnected);
    
Tbegin4=millis();
Serial.print("************************************Tbegin4 =");Serial.println(Tbegin4);

    int i=0;
    while (client.connected() && i< union_size) {            // loop while a client is connected
         if (client.available()) {                           // if there's bytes to read from the client,
             EUI_Packet_Buffer.byteArray[i]=client.read();   // read those and put it in a temporary Blockchain EUI object
             i++;
         }
      }
Treception=millis()-Tbegin4;
Serial.print("************************************Treception =");Serial.println(Treception);
      
     CurrentEUI_SerialPrint_RAW(EUI_Packet_Buffer); //Print the external Packet received
Tbegin5=millis();
Serial.print("************************************Tbegin5 =");Serial.println(Tbegin5);

     if(EUI_Packet_Verify(EUI_Packet_Buffer)){//if verified, add to local chain
Tverify=millis()-Tbegin5;
Serial.print("************************************Tverify =");Serial.println(Tverify);
     Serial.println("****************************************EXTERNAL PACKET VERIFIED ");
     //BLINK(5,500);//Benchmark

 
Tbegin10=millis();
Serial.print("************************************Tbegin10 =");Serial.println(Tbegin10);

     AddExternalEventToLocal(EUI_Packet_Buffer);
    
Taddexternal=millis()-Tbegin10;
Serial.print("************************************Taddexternal =");Serial.println(Taddexternal);

     Serial.println("LOCAL BLOCKCHAIN IS NOW: ");
     Blockchain_SerialPrint();
     }

     
      Serial.println("Ended reading, closing and flushing client");
      client.flush();
      client.stop();
      //WiFi.end();
  }
    //Serial.println("closing and flushing ghost clients");
    client.flush();
    client.stop();
  
    //**** Here I check if some local event has risen in the meanwhile. If so, I put it to the chain, then 
    //I become Client, connect to sibling servers and inform them of my last EUI.
    if (LocalEvent()){
      client.flush();
      client.stop();
      WiFi.end();
      //WiFi.disconnect();   
		  BlockchainClientOnce();
    }
//Tidle=millis()-Tbegin9;
//Serial.print("************************************Tidle =");Serial.println(Tidle);
}

//======================================================================================
void printWifiStatus() {
  // print the SSID of the network you're attached to:
  Serial.print("SSID: ");
  Serial.println(WiFi.SSID());

  // print your WiFi shield's IP address:
  IPAddress ip = WiFi.localIP();
  Serial.print("IP Address: ");
  Serial.println(ip);

  // print the received signal strength:
  long rssi = WiFi.RSSI();
  Serial.print("signal strength (RSSI):"); Serial.print(rssi); Serial.println(" dBm");
  // print where to go in a browser:
  Serial.print("To see this page in action, open a browser to http://");
  Serial.println(ip);
}
//======================================================================================
void UpdateNeigbohood(){//scan all WiFi networks to get the pattern "IoT_BlockchainNode_" followed by an integer (0 to 2^16)
//initially do nothing, only OtherNode will be server
}

//****************************************************************************************************************
//Communications END
//****************************************************************************************************************



//****************************************************************************************************************
//PPKI start
//****************************************************************************************************************
//=========================================================================================================
unsigned long modMult(unsigned long a, unsigned long b, unsigned long mod) //modulo multiplication function
{ 
    unsigned long res = 0; // Initialize result 
    a = a % mod; 
    while (b > 0) 
    { 
        // If b is odd, add 'a' to result 
        if (b % 2 == 1) 
            res = (res + a) % mod; 
  
        // Multiply 'a' with 2 
        a = (a * 2) % mod;   
        // Divide b by 2 
        b /= 2; 
    } 
  
    // Return result 
    return res % mod;
} 

//=========================================================================================================
bool prime(unsigned long number) //primality check for prime numbers
{
   
     for (unsigned long i = 2; i <=sqrt(number); ++i) 
        {
            if (number % i == 0) 
            {
                return false;
            }
         }
        return true;
  }

//=========================================================================================
unsigned long PRN()   //generation of a random prime number
{
 unsigned long n1;
 do
  { 
    randomSeed(analogRead(0));
    n1 = random(170,250); //margins to keep Field and phi product in Unsigned Long Range, to limit "Field parameter" in 16 bit range (up to 65.536).
   }while(n1==0||prime(n1)==false); 
   return n1;
}

//=========================================================================================
unsigned long gcd(unsigned long a, unsigned long b) //function to check GCD
{ 
    unsigned long temp; 
    while (1) 
    { 
        temp = a%b; 
        if (temp == 0) 
         return b; 

       a = b; 
       b = temp;
         
    } 
} 

//=========================================================================================
unsigned long E_gen(unsigned long n, unsigned long phi)   //publickey generation e
{
    for(unsigned long i=210; i<n; i++) // i=2 produces allways too small public keys
     {
       if(gcd(i,n)==1 && gcd(i,phi)==1)
       {
         return i;
         Serial.print("Public key generated: ");
         Serial.println(i);
         //break;
       }
     }
 }

//=========================================================================================
unsigned long D_gen(unsigned long en, unsigned long phi) //privatekey generation d
{
      for(unsigned long i=2; i<phi; i++)
      {
        if(modMult(en,i,phi)==1)
        {
          return i;
          Serial.print("Private key generated: ");
          Serial.println(i);
          //break;
        }
  }
}
  
//=========================================================================================
unsigned long power(unsigned long base, unsigned long expo, unsigned long mod)  
{  
    unsigned long test;
    for(test = 1; expo; expo >>= 1)
    {
        if (expo & 1)
            test = (test * base) % mod;
        base = (base * base) % mod;
    }
    return test;
} 

//=========================================================================================
void PpkiSetup() //Initiate Public/Private Key pair
{  
   delay(2000);//for user to turn on serial monitor
   pinMode(LED_BUILTIN, OUTPUT); 
   BLINK(3,2000);
 
   Serial.begin(9600);
   Firstprime=PRN();
   Serial.println(Firstprime);
   do
   {  
     Secondprime=PRN();
     Serial.println(Secondprime);
   }while(Firstprime==Secondprime||Firstprime*Secondprime<32768); 
   Field=Firstprime*Secondprime;
   phin=(Firstprime-1)*(Secondprime-1);
   Serial.println("calling E_gen:");
   Serial.println(Field);
   Serial.println(phin);
 //Publickey=E_gen(Field, phin);
   Publickey=DevID; //Public key is replaced by DevID, convenient for testing
   Privatekey=D_gen(Publickey,phin);  
}

//=========================================================================================
void PpkiExecute() // run only to test the PPki and to demonstrate the encryption-decryption process 
{ 
  //digitalWrite(LED_BUILTIN, HIGH); pinMode(LED_BUILTIN, OUTPUT); BLINK(1,300); //Debug usage
  //Here i call call the hashing function to bind internal chain-links
  
  /*Here I must also call a read latest block in chain function to sync with siblings*/
  
  if(Hasrun==false && FalseFound==false)
  {
    BLINK(1,100);
    Serial.print("PPKI DeviceID:");Serial.print(DevID);Serial.print("Public key is:");Serial.println(Publickey);Serial.print("Private key is:"); Serial.println(Privatekey);
    Serial.print("Encrypting...Text: "); Serial.println(Text);
    //Enc =  power(Text, Publickey, Field); 
    Enc =  power(Text, Privatekey, Field); //here i "sign" the Text
    Serial.print("Chiper:"); Serial.println(Enc);
    Serial.print("Decrypting...Text= "); 
    //Dec=power(Enc,Privatekey, Field);
    Dec=power(Enc,Publickey, Field); //this has to be executed on the other side
    Serial.println(Dec);
    /*Serial.println(p);
    Serial.println(q);*/
    //delay(10);
    if (Text==Dec && FalseFound==false) {
      //Serial.print(Text);
      Serial.println(" SUCCESS!");
      Success++;
    }
    if (Text!=Dec) {
      FalseFound=true;FirstFailure = Text;
      Serial.print(Text);
      Serial.println(" FAILURE!");
      Serial.print("Public key is:");Serial.println(Publickey);Serial.print("Private key is:"); Serial.println(Privatekey);Serial.print("Field_parameter is:");
      Serial.println(Field);Serial.print("Fhin_parameter is:");Serial.println(phin);
      //BLINK(300,300);
    }
    //Text++;
  }
}
//****************************************************************************************************************
//PPKI END
//****************************************************************************************************************




//****************************************************************************************************************
//Blockchain Events (EUI)adding and handling   START
//****************************************************************************************************************

//====================================Initialize my EUI Packet in here. Absolutely essential.
EUI_Packet EUI_Packet_Initialize(EUI_Packet TempEUIPacket){ //Initialize EUI_Packet to hash, encode, transmit, store
  int i=0,j=0,k=0;
  TempEUIPacket.EventObject.DeviceID=2;
  TempEUIPacket.EventObject.PublicKey=Publickey;
  TempEUIPacket.EventObject.Field=Field;
  TempEUIPacket.EventObject.LocalEventCounter=LocalEventCounter;
  TempEUIPacket.EventObject.EventData=EventData;
  TempEUIPacket.EventObject.LastExternalDeviceID=LastExternalDeviceID;
  for (i=0;i<32;i++){TempEUIPacket.EventObject.HashLastExternal[i]=HashLastExternal[i];}
  Serial.print("LocalEventCounter: "); Serial.println(LocalEventCounter);
  if (LocalEventCounter>0){//Copy The previous EUI hash to the current EUI
    for (i=0;i<32;i++){
      TempEUIPacket.EventObject.HashPrevInternal[i]=Blockchain[LastEventCursor].EventObject.HashLastInternal[i];} 
  }else{
    for (i=0;i<32;i++){TempEUIPacket.EventObject.HashPrevInternal[i]=i;}
    }  
   //Serial.print("TempEUIPacket.EventObject.HashPrevInternal: ");Serial.println(TempEUIPacket.EventObject.HashPrevInternal);

Tbegin7=millis();
Serial.print("************************************Tbegin7 =");Serial.println(Tbegin7);


  Sha256.init();//calculate internal hash and add it to the EUI

  Serial.println("I am hashing");
  for (j=0; j<112; j++){Sha256.print(TempEUIPacket.byteArray[j]);}
  uint8_t * result = Sha256.result();
// for (int i = 0; i < 32; i++) {Serial.print((char)pgm_read_byte(hexMap + (result[i] >> 4)));Serial.print((char)pgm_read_byte(hexMap + (result[i] & 0xf))); }
  for(j=0;j<32;j++){TempEUIPacket.EventObject.HashLastInternal[j]=result[j];}// write back the result of the hash to the EUI package
Thash=millis()-Tbegin7;
Serial.print("************************************Thash =");Serial.println(Thash);


  //Encrypt (sign) current EUI Hash 
  Serial.println("I am Encrypting");
  for(j=0;j<32;j++){Serial.print(TempEUIPacket.EventObject.HashLastInternal[j]);Serial.print("\t");} // the bytes of the hashLastInternal
  Serial.println();
Tbegin8=millis();
Serial.print("************************************Tbegin8 =");Serial.println(Tbegin8);

  for(j=0;j<32;j++){
    TempEUIPacket.EventObject.HashLastInternalSigned[j]=power(TempEUIPacket.EventObject.HashLastInternal[j],Privatekey, Field);
  }
Tsign=millis()-Tbegin8;
Serial.print("************************************Tsign =");Serial.println(Tsign);
  
//  Signature Verification printouts
//  for(j=0;j<32;j++){Serial.print(TempEUIPacket.EventObject.HashLastInternalSigned[j]);Serial.print("\t");}
//  Serial.println();
//  Serial.println("I am Verrifying that HashLast :");  
//  for(j=0;j<32;j++){Serial.print(TempEUIPacket.EventObject.HashLastInternal[j]);Serial.print("\t");} // the bytes of the hashLastInternal
//  Serial.println();Serial.println("Encrypted as:");
//  for(j=0;j<32;j++){Serial.print(TempEUIPacket.EventObject.HashLastInternalSigned[j]);Serial.print("\t");}
//  Serial.println();Serial.println("Decrypts as:");
//  for(j=0;j<32;j++){Serial.print(power(TempEUIPacket.EventObject.HashLastInternalSigned[j], Publickey, Field));Serial.print("\t");}
//  Serial.println();
  
  
  //for(j=0;j<32;j++){VerificationBuffer[j]=power(TempEUIPacket.EventObject.HashLastInternalSigned[j],Publickey, Field);}
  //for(j=0;j<32;j++){Serial.print(power(TempEUIPacket.EventObject.HashLastInternalSigned[j],Publickey, Field));Serial.print("\t");} //printing decrypted hash
  Serial.println();
  
  EUI_Packet_Verify(TempEUIPacket); //debug
  return(TempEUIPacket);
}



//=========================================================================================
bool EUI_Packet_Verify(EUI_Packet TempEUIPacket){
bool verified=true;
int j=0;
  while (j<32 && verified){
    verified=TempEUIPacket.EventObject.HashLastInternal[j]==(byte)power(TempEUIPacket.EventObject.HashLastInternalSigned[j], TempEUIPacket.EventObject.PublicKey, TempEUIPacket.EventObject.Field);
    j++;
  }
Serial.print("Event_package Verified "); Serial.println(verified);Serial.println();
return(verified);
}



//=========================================================================================
void CurrentEUI_SerialPrint(EUI_Packet Temp_EUI){
    int i=0;
    Serial.begin(9600);
//while (!Serial) {
//; // wait for serial port to connect. Needed for native USB port only
// }
    Serial.print("CurrentNodeEUI: ");Serial.println(Temp_EUI.EventObject.DeviceID);
    Serial.print("DeviceID: ");Serial.println(Temp_EUI.EventObject.DeviceID);
    Serial.print("PublicKey: ");Serial.println(Temp_EUI.EventObject.PublicKey); 
    Serial.print("Field: ");Serial.println(Temp_EUI.EventObject.Field); 
    Serial.print("LocalEventCounter: "); Serial.println(Temp_EUI.EventObject.LocalEventCounter);
    Serial.print("EventData: ");Serial.println(Temp_EUI.EventObject.EventData);
    Serial.print("LastExternalDeviceID: "); Serial.println(Temp_EUI.EventObject.LastExternalDeviceID);
    Serial.print("HashLastExternal: ");for (i=0;i<32;i++){Serial.print(Temp_EUI.EventObject.HashLastExternal[i]);};Serial.println();
    Serial.print("HashPrevInternal: ");for (i=0;i<32;i++){Serial.print(Temp_EUI.EventObject.HashPrevInternal[i]);};Serial.println();
    Serial.print("HashLastInternal: ");for (i=0;i<32;i++){Serial.print(Temp_EUI.EventObject.HashLastInternal[i]);};Serial.println();
    Serial.print("HashLastInternalSigned: ");for (i=0;i<32;i++){Serial.print(Temp_EUI.EventObject.HashLastInternalSigned[i]);};Serial.println();
    Serial.println();
} 


//=========================================================================================
void CurrentEUI_SerialPrint_RAW(EUI_Packet Temp_EUI){//printing a single continous stream of the current EUI
    int i;    
    Serial.print(Temp_EUI.EventObject.DeviceID);Serial.print(Temp_EUI.EventObject.DeviceID);Serial.print(Temp_EUI.EventObject.PublicKey);Serial.println(Temp_EUI.EventObject.Field);Serial.print(Temp_EUI.EventObject.LocalEventCounter);
    Serial.print(Temp_EUI.EventObject.EventData);Serial.print(Temp_EUI.EventObject.LastExternalDeviceID);
    for (i=0;i<32;i++){Serial.print(Temp_EUI.EventObject.HashLastExternal[i]);};for (i=0;i<32;i++){Serial.print(Temp_EUI.EventObject.HashPrevInternal[i]);}for (i=0;i<32;i++){Serial.print(Temp_EUI.EventObject.HashLastInternal[i]);}for (i=0;i<32;i++){Serial.print(Temp_EUI.EventObject.HashLastInternalSigned[i]);}
    Serial.println();
    Serial.print("The event in Bytes: ");Serial.println(union_size);
    for(int i=0; i < union_size; i++)
    {
      Serial.print(Temp_EUI.byteArray[i]);
      Serial.print("\t");
    } 
}


//=========================================================================================
void Blockchain_SerialPrint(){ // Serial print the entire local chain
  int i, Head, Tail;//Head the newest and Tail the oldest event in the chain
  Serial.println("******************************BLOCKCHAIN START"); 
  if (LocalEventCounter>0){
    int c;
    for (i=1;i<LocalChainMaxLength+1;i++){
      c=(LastEventCursor+i)%LocalChainMaxLength;
      CurrentEUI_SerialPrint(Blockchain[c]);
    }
  }
  Serial.println("******************************BLOCKCHAIN END"); 
}


//=========================================================================================
void AddEventToLocal(EUI_Packet Temp_EUI){ // this adds an event to Local Chain. If events are exeeding the LocalChainMaxLength then it goes round from the beginning
    //check length
Tbegin6=millis();
Serial.print("************************************Tbegin6 =");Serial.println(Tbegin6);

    LastEventCursor=LocalEventCounter%LocalChainMaxLength; 
    Blockchain[LastEventCursor]=Temp_EUI;
    CurrentEUI_SerialPrint(Blockchain[LastEventCursor]);
    LocalEventCounter++;

Tcopy=millis()-Tbegin6;
Serial.print("************************************Tcopy =");Serial.println(Tcopy);
}


//=========================================================================================
void AddExternalEventToLocal(EUI_Packet Temp_EUI){
  int i,j;
  for (i=0;i<32;i++){HashLastExternal[i]=Temp_EUI.EventObject.HashLastInternal[i];}
  for (i=0;i<32;i++){Temp_EUI.EventObject.HashLastExternal[i]=HashLastExternal[i];}
  //memcpy(HashLastExternal, Temp_EUI.EventObject.HashLastInternal, sizeof(HashLastExternal));//update the last external event
  LastExternalDeviceID=Temp_EUI.EventObject.DeviceID;
  Temp_EUI.EventObject.DeviceID=LastExternalDeviceID;
  Temp_EUI.EventObject.PublicKey=Publickey; //Sign it with my key now
  Temp_EUI.EventObject.Field=Field;   
  if (LocalEventCounter>0){//Copy The previous EUI hash of the local chain to the current EUI
    for (i=0;i<32;i++){Temp_EUI.EventObject.HashPrevInternal[i]=Blockchain[LastEventCursor].EventObject.HashLastInternal[i];} 
  }else{
    for (i=0;i<32;i++){Temp_EUI.EventObject.HashPrevInternal[i]=i;}}  
     
  Sha256.init();//calculate internal hash and add it to the EUI
  Serial.println("I am hashing ");
  for (j=0; j<112; j++){Sha256.print(Temp_EUI.byteArray[j]);}
  uint8_t * result = Sha256.result();
  for(j=0;j<32;j++){Temp_EUI.EventObject.HashLastInternal[j]=result[j];}// write back the result of the hash to the EUI package
    //Encrypt (sign) current EUI Hash 
  Serial.println("I am Encrypting");
  for(j=0;j<32;j++){Serial.print(Temp_EUI.EventObject.HashLastInternal[j]);Serial.print("\t");} // the bytes of the hashLastInternal
  Serial.println();
  for(j=0;j<32;j++){
    Temp_EUI.EventObject.HashLastInternalSigned[j]=power(Temp_EUI.EventObject.HashLastInternal[j],Privatekey, Field);
   }
    if (EUI_Packet_Verify(Temp_EUI)){
     AddEventToLocal(Temp_EUI); //I signed and adding an external event to my chain
    }
    else { 
      Serial.println("Something Went Wrong in Adding Exernal");} 

 }


//=========================================================================================
//Scanning for local Events. For debugging a random number is the "switch to client". Chances of new local event are explored here.
bool LocalEvent(){
//Lets fake it: every HAT itereations, an event occures
   TotalHats++;
     if ((millis()-LastLocalEventMillis)>HAT) {//run on every HAT miliseconds
     LastLocalEventMillis=millis();
     EventData=LastLocalEventMillis;
     
     Serial.print("***Got a Local Event, with Data:");Serial.println(LastLocalEventMillis);
     Serial.print("*******Adding to local Blockchain");
     CurrentEUIPacket=EUI_Packet_Initialize(CurrentEUIPacket);
     AddEventToLocal(CurrentEUIPacket);
     return(true);
   
//   if (TotalHats % HAT ==0){//run on every HAT
//	   EventData=TotalHats;
//	   Serial.print("***Got a Local Event, with Data:");Serial.println(TotalHats);
//     Serial.print("*******Adding to local Blockchain");
//     CurrentEUIPacket=EUI_Packet_Initialize(CurrentEUIPacket);
//     AddEventToLocal(CurrentEUIPacket);
//	   return(true);
 /*    randomSeed(analogRead(0));
   int i = random(1,100);
   if (i>70){
		Serial.print("***Got a Local Event, with Data:");Serial.println(i);
		EventData=i;
		CurrentEUIPacket=EUI_Packet_Initialize(CurrentEUIPacket);
	   //CurrentEUI=EUI_Calculate(LastEventCursor);
	   AddEventToLocal(CurrentEUIPacket);return(true); */
   }
   else{
   return(false);
   }
}

//****************************************************************************************************************
//Blockchain handling   END
//****************************************************************************************************************



//============================================================================================================
void BLINK(int i,int myDelay){ // Debug flashing the LED
int k;
pinMode(LED_BUILTIN, OUTPUT); 
for (k=1;k<i;k++){
    digitalWrite(LED_BUILTIN, HIGH);  // turn the LED on (HIGH is the voltage level)
    delay(myDelay);                       // wait for half a second
    digitalWrite(LED_BUILTIN, LOW);  // turn the LED on (HIGH is the voltage level)
    delay(myDelay); 
  }
}



//****************************************************************************************************************
//Let the show begin: Here is the entry point of this sketch.
//****************************************************************************************************************

//=========================================================================================
void setup() {
int i;
BLINK(3,500);// Let user know I am awake
delay(1000);
Serial.print("I am AWAKE and picking my PP Keys");
PpkiSetup();
Serial.print("My Keys are: Public: ");Serial.print(Publickey);Serial.print(" Private: ");Serial.println(Privatekey);
Serial.println("Lets put some test objects in the Local chain");

for (i=0;i<24;i++){ // Populate local Blockchain with some Event objects (EUI Packets)
 EventData=i;
  CurrentEUIPacket=EUI_Packet_Initialize(CurrentEUIPacket);
  //CurrentEUI=EUI_Calculate(LastEventCursor);
  AddEventToLocal(CurrentEUIPacket);
}

Serial.begin(9600);
//while (!Serial) {
//; // wait for serial port to connect. Needed for native USB port only
// }
Tbegin=millis();
Serial.print("************************************Tbegin =");Serial.println(Tbegin);
BlockchainServerSetup();
Tcs=millis()-Tbegin;
Serial.print("************************************Tcs =");Serial.println(Tcs);
IamServer=true;
}

//=========================================================================================
void loop() {// By default I am on Server mode. The mode only toggles if a Local Event rises, which is cheked in BlockchainServerLoop()
//***Wifi AP and http Server - is everyones Default Status 
if (IamServer==false){
  BlockchainServerSetup();
}

BlockchainServerLoop(); 

}
