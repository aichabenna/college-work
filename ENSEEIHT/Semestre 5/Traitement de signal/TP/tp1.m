% Nombre d'échantillons
N = 90; 

%%%%%%%%%%%%%%% Représentation temporelle %%%%%%%%%%%%%%%

f0 = 1100;
% Cas 1 : Question 1 et 2 
Fe1 = 10000;
Te1 = 1/Fe1;

% 0 début Te Pas (n-1)*Te Fin
t1 = [0:Te1:(N-1)*Te1];
x1 = cos (2*pi*f0*t1);

figure;
subplot(2,3,1);
plot(t,x1);
xlabel("Temps en s");
ylabel("x");

% Cas 2 : Question 3
Fe2 = 1000;
Te2 = 1 / Fe2;

t2 = [0:Te2:(N-1)*Te2];
x2 = cos (2*pi*f0*t2);
subplot(2,3,4);
plot(t,x2);
xlabel("Temps en s");
ylabel("x");

% Question 4 
% on trouve f = 100 \ = de f0 parce qu'on ne respecte pas 
% la condition de Shanon

%%%%%%%%%%%%%%% Représentation fréquentielle %%%%%%%%%%%%%%%

% fft(x) Transformée de fourrier de cosinus
TF1 = fft(x1);
f1 = [0: Fe1/(N-1) :Fe1];
subplot(2,3,2);
semilogy(f1, abs(TF1));
xlabel("Fréquence en Hz");
ylabel("X");

TF2 = fft(x2);
f2 = [0: Fe2/(N-1) :Fe2];
subplot(2,3,5);
semilogy(f2, abs(TF2));
xlabel("Fréquence en Hz");
ylabel("X");

%%%%%%%%%%%%%%%%%%%%%%%%% Zero Padding %%%%%%%%%%%%%%%%%%%%%%%%

Zp1 = 2^(nextpow2(N));
TF1 = fft(x1, Zp1); 
f1 = [0: Fe1/(Zp1-1) :Fe1];
subplot(2,3,3);
semilogy(f1, abs(TF1));
xlabel("Fréquence en Hz");
ylabel("X");

Zp2 = 2^(nextpow2(N));
TF2 = fft(x2, Zp2); 
f2 = [0: Fe2/(Zp2-1) :Fe2];
subplot(2,3,6);
semilogy(f2, abs(TF2));
xlabel("Fréquence en Hz");
ylabel("X");

%%%%%%%%% DSP : Densité Spectrale de Puissance  %%%%%%%%%%%%%%%
% Coisissez un des cosinus générés précédemment, estimez, puis 
% tracez,sa DSP

% Périodogramme
% Corrélogramme
% Périodogramme de Welch

