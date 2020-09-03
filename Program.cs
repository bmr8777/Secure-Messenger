using System;
using System.Net.Http;
using System.Net.Http.Headers;
using System.Text;
using System.Threading.Tasks;
using System.Security.Cryptography;
using System.Numerics;
using System.IO;
using Newtonsoft.Json;

// Name: Brennan Reed <@bmr8777@rit.edu>
// Date: 3/23/20
// Class: CSCI-251
// Assignment: Secure Messaging Project

namespace Messenger
{

    /// <summary>
    ///     Static class which contains the BigInteger extension method IsProbablyPrime()
    /// </summary>
    
    static class BigIntegerExtension
    {
        /// <summary>
        ///     Extension method for BigIntegers that determines the primality of value
        /// </summary>
        /// <param name="value">
        ///     Value of the BigInteger
        /// </param>
        /// <param name="witnesses"></param>
        /// <returns>
        ///     Whether value is prime
        /// </returns>

        public static Boolean IsProbablyPrime(this BigInteger value, int witnesses = 10)
        {
            if (value <= 1) return false;

            if (witnesses <= 0) witnesses = 10;

            BigInteger d = value - 1;
            int s = 0;

            while (d % 2 == 0)
            {
                d /= 2;
                s += 1;
            }

            Byte[] bytes = new Byte[value.ToByteArray().LongLength];
            BigInteger a;

            for (int i = 0; i < witnesses; i++)
            {
                do
                {
                    var Gen = new Random();
                    Gen.NextBytes(bytes);
                    a = new BigInteger(bytes);
                }
                while (a < 2 || a >= value - 2);
                BigInteger x = BigInteger.ModPow(a, d, value);
                if (x == 1 || x == value - 1) continue;
                for (int r = 1; r < s; r++)
                {
                    x = BigInteger.ModPow(x, 2, value);
                    if (x == 1) return false;
                    if (x == value - 1) break;
                }
                if (x != value - 1) return false;
            }
            return true;
        }
    }

    /// <summary>
    ///     Static Class used for generating the prime numbers needed to create RSA Keys
    /// </summary>

    static class PrimeGenerator
    {
        /// <summary>
        ///     Uses a Parallel.For loop to generate numbers and determines their primality using IsProbablyPrime()
        /// </summary>
        /// <param name="bits">
        ///     The specified number of bits for the prime number
        /// </param>
        /// <returns>
        ///     random prime number
        /// </returns>

        public static BigInteger GeneratePrime(long bits)
        {
            BigInteger b = new BigInteger(0);
            Parallel.For(0, 100000, (i, loopState) => 
            {
                var rng = new RNGCryptoServiceProvider();
                byte[] bytes = new byte[bits / 8];
                rng.GetBytes(bytes);
                var bi = new BigInteger(bytes); // randomly generated number
                if (bi.IsProbablyPrime()) // checks if the number is prime
                {
                    b = bi;
                    loopState.Stop();
                }
            });
            return b;
        }
    }

    /// <summary>
    ///     Object that stores an email, and a string representing a public.key
    /// </summary>

    public class Key
    {
        /// <summary>
        ///     Creates a new Key Object
        /// </summary>
        /// <param name="email_">
        ///     the email address for the key
        /// </param>
        /// <param name="key_">
        ///     string representation of the public.key
        /// </param>

        public Key(string email_, string key_)
        {
            email = email_;
            key = key_;
        }

        public string email; // the corresponding email address for the key
        public string key; // string representation of the public.key
    }

    /// <summary>
    ///     Object that stores an email, and an encrypted message
    /// </summary>

    public class Message 
    {
        /// <summary>
        ///     Creates a new instance of a Message Object
        /// </summary>
        /// <param name="email_">
        ///     the email address for the message
        /// </param>
        /// <param name="content_">
        ///     the encrypted text for the message
        /// </param>
        
        public Message(string email_, string content_)
        {
            email = email_;
            content = content_;
        }

        public string email; // email address corresponding to the message
        public string content; // encrypted text for the message
    }

    /// <summary>
    ///     Class which holds the logic, and necessary attributes to generate, encrypt, and decrypt
    ///     messages using RSA keys
    /// </summary>

    class Program
    {

        private long keysize; // specified key length
        private string email; // specified email address
        private string plaintext; // plaintext of the message being sent
        private BigInteger N;
        private BigInteger E;
        private BigInteger D;

        /// <summary>
        ///     Creates a new Program Object given the keySize
        /// </summary>
        /// <param name="keysize_">
        ///     number of bytes in the RSA key
        /// </param>
        
        Program(long keysize_)
        {
            keysize = keysize_;
        }

        /// <summary>
        ///     Creates a new Program Object given an email
        /// </summary>
        /// <param name="email_">
        ///     the email address for the program
        /// </param>

        Program(string email_)
        {
            email = email_;
        }

        /// <summary>
        ///     Creates a new Program Object given an email, and a plaintext message
        /// </summary>
        /// <param name="email_">
        ///     the email address to send the message to
        /// </param>
        /// <param name="plaintext_">
        ///     the plaintext version of the message to be encrypted
        /// </param>

        Program(string email_, string plaintext_)
        {
            email = email_;
            plaintext = plaintext_;
        }

        /// <summary>
        ///     Calculates the necessary values to create an RSA key pair
        /// </summary>
        /// <param name="p">
        ///     prime number used in the calculations
        /// </param>
        /// <param name="q">
        ///     prime number used in the calculations
        /// </param>

        void RsaKeyGenerator(BigInteger p, BigInteger q)
        {
            N = p * q;
            BigInteger r = (p - 1) * (q - 1);
            E = PrimeGenerator.GeneratePrime(64);
            D = ModInverse(E,r);
        }

        /// <summary>
        ///     
        /// </summary>
        /// <param name="a">
        ///     prime number
        /// </param>
        /// <param name="n">
        ///     prime number
        /// </param>
        /// <returns>
        ///     the modular inverse of (a, b)
        /// </returns>

        BigInteger ModInverse(BigInteger a, BigInteger n)
        {
            BigInteger i = n, v = 0, d = 1;
            while (a > 0)
            {
                BigInteger t = i/a, x = a;
                a = i % x;
                i = x;
                x = d;
                d = v - t*x;
                v = x; 
            }
            v %= n;
            if (v < 0)
                v = (v + n) % n;
            return v;
        }

        /// <summary>
        ///     Calculates the attribute values required to encrypt/decrypt a message for a particular user
        /// </summary>
        /// <param name="email">
        ///     the user's email
        /// </param>

        void GetEncryptionValues(string email)
        {
            string publicKey, privateKey;
            bool decryption = false;
            bool littleEndian = BitConverter.IsLittleEndian;

            if (String.Equals(email, "decryption"))
            {
                publicKey = File.ReadAllText("public.key");
                decryption = true;
            }
            else
            {
                if (!File.Exists(email + ".key"))
                {
                    Console.WriteLine("Key does not exist for " + email);
                    Environment.Exit(-1);
                }
                using (StreamReader r = new StreamReader(email + ".key"))
                    publicKey = r.ReadLine(); // only reads the first key stored if there are multiple
            }
     
            byte[] publicBytes = Convert.FromBase64String(publicKey);
            byte[] eLengthBytes = new byte[4];
            byte[] nLengthBytes = new byte[4];

            byte[] eBytes;
            byte[] nBytes;

            Buffer.BlockCopy(publicBytes, 0, eLengthBytes, 0, 4); // get the length of E
            if (littleEndian)
                Array.Reverse(eLengthBytes);
            int eLength = BitConverter.ToInt32(eLengthBytes);
            if (eLength > 1000)
            {
                Array.Reverse(eLengthBytes);
                eLength = BitConverter.ToInt32(eLengthBytes);
            }
            eBytes = new byte[eLength];

            Buffer.BlockCopy(publicBytes, 4 + eLength, nLengthBytes, 0, 4);
            if (littleEndian)
                Array.Reverse(nLengthBytes);
            int nLength = BitConverter.ToInt32(nLengthBytes);
            if (nLength > 1000)
            {
                Array.Reverse(nLengthBytes);
                nLength = BitConverter.ToInt32(nLengthBytes);
            }
            nBytes = new byte[nLength];

            Buffer.BlockCopy(publicBytes, 4, eBytes, 0, eLength);
            Buffer.BlockCopy(publicBytes, 8 + eLength, nBytes, 0, nLength);

            N = new BigInteger(nBytes);
            E = new BigInteger(eBytes);

            if (decryption)
            {
                if (!File.Exists("private.key"))
                {
                    //Console.WriteLine("ERROR: The private.key can't be found.");
                    Environment.Exit(-1);
                }

                using (StreamReader sr = new StreamReader("private.key"))
                {
                    privateKey = sr.ReadLine();
                }

                byte[] dBytes;
                byte[] dLengthBytes = new byte[4];
                byte[] privateBytes = Convert.FromBase64String(privateKey);
                Buffer.BlockCopy(privateBytes, 0, dLengthBytes, 0, 4);
                if (littleEndian)
                    Array.Reverse(dLengthBytes);
                int dLength = BitConverter.ToInt32(dLengthBytes);
                if (dLength > 100)
                {
                    Array.Reverse(dLengthBytes);
                    dLength = BitConverter.ToInt32(dLengthBytes);
                }
                dBytes = new byte[dLength];
                Buffer.BlockCopy(privateBytes, 4 + dLength, nLengthBytes, 0, 4);
                Buffer.BlockCopy(privateBytes, 4, dBytes, 0, dLength);
                Buffer.BlockCopy(privateBytes, 8 + dLength, nBytes, 0, nLength);

                D = new BigInteger(dBytes);
            }  
        }

        /// <summary>
        ///     Encrypts a plain text message using the specified rsa key
        /// </summary>
        /// <param name="plainText">
        ///     unencrypted message
        /// </param>
        /// <param name="email">
        ///     email of the message recipient
        /// </param>
        /// <returns>
        ///     encrypted message
        /// </returns>

       string EncryptMessage (string plainText, string email)
       {
            byte[] b;
            byte[] m = Encoding.UTF8.GetBytes(plainText);
            BigInteger c = new BigInteger(m);

            GetEncryptionValues(email);

            c = BigInteger.ModPow(c, E, N);
            b = c.ToByteArray();
            return Convert.ToBase64String(b);
       }

        /// <summary>
        ///     Decrypts a message using the private key
        /// </summary>
        /// <param name="encryptedText">
        ///     encrypted message
        /// </param>
        /// <returns>
        ///     decrypted message
        /// </returns>

        string DecryptMessage (string encryptedText)
        {
            byte[] m = Convert.FromBase64String(encryptedText);
            byte[] temp;
            BigInteger c = new BigInteger(m);

            GetEncryptionValues("decryption");
            c = BigInteger.ModPow(c, D, N);

            temp = c.ToByteArray();
            return Encoding.UTF8.GetString(temp);
        }

        /// <summary>
        ///     Displays the usage information for the program to the user
        /// </summary>

        static void DisplayUsageInformation()
        {
            Console.WriteLine("Usage: dotnet run <option> <other arguments>");
            Console.WriteLine("\t  - <option> - desired task for the program to complete");
            Console.WriteLine("\t  - <other arguments> - arguments specific to the desired task");
            Console.WriteLine("\nProgram Options: ");
            Console.WriteLine("\t - keyGen keysize - Generates a keypair (public and private keys) and stores them\n" +
                "\t   locally on the disk(in files called public.key and private.key respectively).");
            Console.WriteLine("\t - sendKey email - Sends the public key to the server. The server will then\n" +
                "\t   then register this email address as a valid receiver of messages. The private key\n" +
                "\t   will remain locally.");
            Console.WriteLine("\t - getKey email - Retrieves a base64 encoded public key for a particular user\n");
            Console.WriteLine("\t - sendMsg email plaintext - this will base64 encode a message for a user in the field.");
            Console.WriteLine("\t - getMsg email - Retrieves a base64 encoded message for a particular user.");
        }

        /// <summary>
        ///     Main program which validates user input, creates instances of the Program Object,
        ///     then instructs it to complete the actions specified by the user
        /// </summary>
        /// <param name="args">
        ///     command line arguments
        /// </param>

            static void Main(string[] args)
        {
            string mode = args[0];

            string uri = "http://kayrun.cs.rit.edu:5000/";
            string email, plainText, responseBody;
            long keySize;

            Program program;
            HttpClient client = new HttpClient();
            HttpResponseMessage responseMessage;
            client.BaseAddress = new Uri(uri);
            client.DefaultRequestHeaders.Accept.Add(new MediaTypeWithQualityHeaderValue("application/json"));

            if (args.Length < 2 || args.Length > 3)
            {
                //Console.WriteLine("ERROR: Invalid number of command line arguments.");
                //DisplayUsageInformation();
                Environment.Exit(-1);
            }
            switch (mode)
            {
                case "keyGen":
                    if (args.Length != 2) // invalid number of arguments
                    {
                        Console.WriteLine("ERROR: Incorrect number of arguments for keyGen.");
                        DisplayUsageInformation();
                        Environment.Exit(-1); // exit the program
                    }
                    if (!Int64.TryParse(args[1], out keySize)) // Check whether <keysize> is a valid number
                    {
                        Console.WriteLine("ERROR: keySize must be a valid number.");
                        Environment.Exit(-1);
                    }
                    program = new Program(keySize);
                    BigInteger p = PrimeGenerator.GeneratePrime(keySize / 2);
                    BigInteger q = PrimeGenerator.GeneratePrime(keySize / 2);

                    program.RsaKeyGenerator(p, q); // Generate the values for the RSA Keys

                    var eBytes = program.E.ToByteArray();
                    var nBytes = program.N.ToByteArray();
                    var dBytes = program.D.ToByteArray();

                    byte[] eLength = BitConverter.GetBytes(eBytes.Length);
                    byte[] nLength = BitConverter.GetBytes(nBytes.Length);
                    byte[] dLength = BitConverter.GetBytes(dBytes.Length);

                    byte[] publicBytes = new byte[eBytes.Length + nBytes.Length + 8];
                    byte[] privateBytes = new byte[dBytes.Length + nBytes.Length + 8];

                    Buffer.BlockCopy(eLength, 0, publicBytes, 0, 4);
                    Buffer.BlockCopy(eBytes, 0, publicBytes, 4, eBytes.Length);
                    Buffer.BlockCopy(nLength, 0, publicBytes, 4 + eBytes.Length, 4);
                    Buffer.BlockCopy(nBytes, 0, publicBytes, eBytes.Length + 8, nBytes.Length);
                    Buffer.BlockCopy(dLength, 0, privateBytes, 0, 4);
                    Buffer.BlockCopy(dBytes, 0, privateBytes, 4, dBytes.Length);
                    Buffer.BlockCopy(nLength, 0, privateBytes, 4 + dBytes.Length, 4);
                    Buffer.BlockCopy(nBytes, 0, privateBytes, dBytes.Length + 8, nBytes.Length);

                    File.WriteAllText("public.key", Convert.ToBase64String(publicBytes));
                    File.WriteAllText("private.key", Convert.ToBase64String(privateBytes));
                    using (StreamWriter sw = File.AppendText("private.key"))
                    {
                        sw.WriteLine("\nValid Email Addresses:"); // add a flag to private.key to indicate where the list of valid email addresses begin
                    }
                    //Console.WriteLine("Keys successfully generated.");
                    break;

                case "sendKey":
                    if (args.Length != 2) // incorrect number of arguments for sendKey
                    {
                        Console.WriteLine("ERROR: Incorrect number of arguments for sendKey.");
                        DisplayUsageInformation();
                        Environment.Exit(-1);
                    }

                    email = args[1];
                    program = new Program(email);
                    if (!File.Exists("private.key"))
                    {
                        //Console.WriteLine("ERROR: There is no private.key stored on the system.");
                        //Console.WriteLine("\t\t Keys must be generated prior to sending them to the server.");
                        Environment.Exit(-1);
                    }
                    using (StreamWriter sw = File.AppendText("private.key"))
                    {
                        sw.WriteLine(email); // add the email as a valid email address
                    }
                    if (!File.Exists("public.key"))
                    {
                        //Console.WriteLine("ERROR: There is no public.key stored on the system.");
                        //Console.WriteLine("\t\t Keys must be generated prior to sending them to the server.");
                        Environment.Exit(-1);
                    }

                    string key = File.ReadAllText("public.key"); // Base64 Encoded key string
                    string message = uri + "Key/" + email; // message being sent to the server

                    string jsonObject = JsonConvert.SerializeObject(new Key(email, key)); // convert the Key to a JSON string
                    var content = new StringContent(jsonObject, Encoding.UTF8,"application/json");

                    try
                    {
                        var response = client.PutAsync(message, content).Result.EnsureSuccessStatusCode();
                    }
                    catch (HttpRequestException)
                    {
                        //Console.WriteLine("ERROR: sendKey unsucessful.");
                        Environment.Exit(-1);
                    }

                    Console.WriteLine("Key saved");
                    break;


                case "getKey": // Functions properly
                    if (args.Length != 2) // incorrect number of arguments
                    {
                        Console.WriteLine("ERROR: Incorrect number of arguments for getKey.");
                        DisplayUsageInformation();
                        Environment.Exit(-1);
                    }

                    email = args[1];
                    program = new Program(email);
                    message = "Key/" + email;
                    string outputPath = email + ".key";

                    try
                    {
                        responseMessage = client.GetAsync(uri + message).Result.EnsureSuccessStatusCode();
                        responseBody = responseMessage.Content.ReadAsStringAsync().Result;
                        Key result = JsonConvert.DeserializeObject<Key>(responseBody); // convert responseBody into a Key Object

                        if (File.Exists(outputPath)) // Check whether the email already has keys stored
                        {
                            using (StreamWriter sw = File.AppendText(outputPath))
                            {
                                sw.WriteLine("\n" + result.key); // add the key to the collection for the email
                            }
                        }
                        else
                            File.WriteAllText(outputPath, result.key);
                    }
                    catch (HttpRequestException)
                    {
                        //Console.WriteLine("getKey was unsucessful.");
                        Environment.Exit(-1);
                    }
                    break;

                case "sendMsg":
                    if (args.Length != 3) // Incorrect number of arguments
                    {
                        Console.WriteLine("Incorrect number of arguments for sendMsg.");
                        DisplayUsageInformation(); // display usage information
                        Environment.Exit(-1); // exit the program
                    }

                    email = args[1];
                    plainText = args[2];
                    message = "Message/" + email;

                    if (!File.Exists(email + ".key")) // No key stored locally for the email: report error and exit
                    {
                        Console.WriteLine("Key does not exist for " + email);
                        Environment.Exit(-1);
                    }
                    program = new Program(email, plainText);

                    string encryptedMessage = program.EncryptMessage(plainText, email);

                    jsonObject = JsonConvert.SerializeObject(new Message(email, encryptedMessage)); // convert the Message to a JSON Object
                    content = new StringContent(jsonObject, Encoding.UTF8, "application/json"); 

                    try
                    {
                        responseMessage = client.PutAsync(message, content).Result.EnsureSuccessStatusCode(); // send the message to the server
                    }
                    catch (HttpRequestException)
                    {
                        //Console.WriteLine("ERROR: sendMsg was unsuccessful.");
                        Environment.Exit(-1);
                    }

                    Console.WriteLine("Message written");
                    break;

                case "getMsg":
                    if (args.Length != 2) // invalid number of arguments
                        break; // report error and display usage details
                    email = args[1];
                    message = "Message/" + email;
                    program = new Program(email);
                    bool validEmail = false;

                    try
                    {
                        responseMessage = client.GetAsync(uri + message).Result.EnsureSuccessStatusCode();
                        responseBody = responseMessage.Content.ReadAsStringAsync().Result;

                        Message resultMessage = JsonConvert.DeserializeObject<Message>(responseBody); // convert the jsonString to a Message

                        using (StreamReader reader = new StreamReader("private.key"))
                        {
                            string line;
                            while ((line = reader.ReadLine()) != null) // read until EOF
                            {
                                if (String.Equals(email, line))
                                {
                                    validEmail = true;
                                    break;
                                }
                            }
                        }
                        if (validEmail)
                            Console.WriteLine(program.DecryptMessage(resultMessage.content)); // decrypt and display the message to the user
                        else
                        {
                            Console.WriteLine("You cannot decode message for emails that you don't have the private.key for.");
                            Environment.Exit(-1);
                        }
                    }
                    catch (HttpRequestException)
                    {
                        //Console.WriteLine("ERROR: getMsg was unsuccessful");
                        Environment.Exit(-1);
                    }
                    break;

                default: // Invalid program mode
                    Console.WriteLine("ERROR: " + mode + " is not a valid program option.");
                    DisplayUsageInformation();
                    break;
            }
        }
    }
}