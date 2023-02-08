clc ;
clear all;
close all;
load donnees1.mat;
load donnees2.mat;

% Messages des utilisateurs
message1 = bits_utilisateur1;
message2 = bits_utilisateur2;
% Fréquence porteuse
fp1 = 0;
fp2 = 46000;
% Durée d'un timeslot
T = 40e-3; 

% Fréquence d'échantillonnage
Fe = 120000;
% Période d'échantillonnage
Te= 1/Fe;

%% 3.1. Modulation bande base

% 1.1. Valeur de Ns
% Nb : Nombre de bits des messages
Nb = numel(message1);
Ts = T/Nb; 
Ns=Ts/Te;

% 1.2. Tracé de m1 et m2 avec une échelle temporelle en secondes
t = [0:Te:T-Te];
figure;

%%%%%%%%%%%%%%%%%%%%%%% m1(t) %%%%%%%%%%%%%%%%%%%%%%%%%
title("Signal m1(t) avec une échelle temporelle");
subplot(2,1,1);
m1 = kron(message1,ones(1,Ns));
plot(t,m1);
xlabel("Temps en s");
ylabel("m1");
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%% m2(t) %%%%%%%%%%%%%%%%%%%%%%%%%

title("Signal m2(t) avec une échelle temporelle");
subplot(2,1,2);
m2 = kron(message2,ones(1,Ns));
plot(t,m2);
xlabel("Temps en s");
ylabel("m2");
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% 1.3. Tracé des DSP des signaux m1(t) et m2(t) avec une
% échelle fréquentielle en Hz

figure;

%%%%%%%%%%%%%%%%%%%%% DSP de m1(t) %%%%%%%%%%%%%%%%%%%%%%
title("DSP du signal m1(t) avec une échelle fréquentielle en Hz");
subplot(211);
DSP1 = 1/numel(m1)*abs(fft(m1)).^2;
f = (0:numel(m1)-1)/numel(m1)*Fe;
semilogy(f,DSP1);
xlabel("Fréquence en Hz");
ylabel("DSP de m1");
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%% DSP de m2(t) %%%%%%%%%%%%%%%%%%%%%%
title("DSP du signal m2(t) avec une échelle fréquentielle en Hz");
subplot(212);
DSP2 = 1/numel(m2) * abs(fft(m2)).^2;
f = (0:numel(m2)-1) / numel(m2) * Fe;
semilogy(f,DSP2);
xlabel("Fréquence en Hz");
ylabel("DSP de m2");
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%% Messages signés %%%%%%%%%%%%%%%%%%%%
m1_signe= 2*m1-1;
m2_signe= 2*m2-1;
figure;
%%%%%%%%%%%%%%%%%%%%% DSP de m1(t) %%%%%%%%%%%%%%%%%%%%%%
title("DSP du signal m1(t) signé avec une échelle fréquentielle en Hz");
subplot(211);
DSP1=1/numel(m1_signe)*abs(fft(m1_signe)).^2;
f=(0:numel(m1_signe)-1)/numel(m1_signe)*Fe;
semilogy(f,DSP1);
xlabel("Fréquence en Hz");
ylabel("DSP de m1");
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%% DSP de m2(t) %%%%%%%%%%%%%%%%%%%%%%
title("DSP du signal m2(t) signé avec une échelle fréquentielle en Hz");
subplot(212);
DSP2=1/numel(m2_signe) * abs(fft(m2_signe)).^2;
f=(0:numel(m2_signe)-1) / numel(m2_signe)* Fe;
semilogy(f,DSP2);
xlabel("Fréquence en Hz");
ylabel("DSP de m2");
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% 3.2. Construction du signal MF-TDMA

% 1. Génerer un signal comportant 5 slots de durée T = 40 ms et placer le message NRZ
% généré précédemment (m1(t) ou m2(t)) et contenant l'information à transmettre dans
% le slot alloué. 

x1 = kron ([0 1 0 0 0], m1);
x2 = kron ([0 0 0 0 1], m2);
m = x1 + x2;

% Tracé le signal résultant avec une échelle temporelle en secondes
t = [0:Te:5*T-Te];
figure;
title("Signal m");
plot(t,m);
xlabel("Temps en s");
ylabel("m");

% En utilisant une modulation d'amplitude, placer, pour chaque utilisateur, le message
% précédemment construit sur la fréquence porteuse allouée. On obtient alors les signaux
% x1(t) et x2(t) de la gure 3.
x1_signe = kron ([0 1 0 0 0], m1_signe);
x2_signe = kron ([0 0 0 0 1], m2_signe);
message_signe = x1_signe.*cos(2*pi*fp1*t) + x2_signe.*cos(2*pi*fp2*t);

% 2. Sommer les signaux x1(t) et x2(t) et ajouter le bruit gaussien afin d'obtenir le signal MF-
% TDMA, x(t), qui sera reçue par la station d'interconnexion. On xera, dans un premier
% temps, un rapport signal sur bruit élevé (par exemple 100 dB). Tracer le signal MF-TDMA
% avec une échelle temporelle en secondes. Le tracé observé est-il conforme à ce qui est at-
% tendu ? Expliquer votre réponse.

Zp = 2^nextpow2(length(message_signe));
SNR = 100;

Ps = mean(abs(message_signe).^2);
Pb = Ps*10.^(-SNR/10);
b = sqrt(Pb) * randn(1,5* Nb*Ns);
message_signe = message_signe+b;

figure;
title("Signal MF-TDMA");
plot(t,message_signe);
xlabel("Temps en s");
ylabel("m");

% 3. Estimer puis tracer la densité spectrale de puissance du signal MF-TDMA avec une échelle
% fréquentielle en Hz. Le tracé observé est-il conforme à l'expression théorique obtenue pré-
% cédemment ? Expliquer votre réponse

DSP=1/numel(message_signe)*abs(fft(message_signe)).^2;
f=(0:numel(message_signe)-1)/numel(message_signe)*Fe;

figure;
semilogy(f,DSP);
title("Densité spectrale de puissance du signal MF-TDMA");
xlabel("Fréquence en Hz");
ylabel("DSP de m");

%% 4. Mise en place du récepteur MF-TDMA
%% 4.1 Démultiplexage des porteuses

%% 4.1.1. Synthèse du filtre passe-bas

% 1. Tracer la réponse impulsionnelle et la réponse en fréquence du filtre implanté.

fc = 23000;
fc_b = fc/Fe;
ordre =61;
h1 = 2 * fc_b * sinc(2* fc_b * [-(ordre -1)/2 : (ordre -1)/2 ]);

figure;
subplot(2,1,1);
plot([-(ordre -1)/2:(ordre -1)/2 ],h1);
title("Réponse impulsionnelle du filtre passe-bas");
xlabel("h1(t)");
ylabel("t");

H1 = fftshift(fft(h1, Zp));
f = linspace(-Fe/2,Fe/2,Zp);
subplot(2,1,2);
semilogy(f,abs(H1));
title("Réponse en fréquence du filtre passe-bas");
xlabel("H1(f)");
ylabel("f");

% 2. Tracer, sur un même graphique, la densité spectrale de puissance du signal MF-TDMA reçu
% et le module de la réponse en fréquences du filtre implanté. 
Rx = 1/Zp * xcorr(message_signe);
Sx = fftshift(fft(Rx,Zp));

module_H1 = abs(H1);
figure;
semilogy(f, abs(Sx));
title("DSP du signal du signal MF-TDMA et |H(f)|^2");
xlabel("Sx(f) / |H(f)|^2");
ylabel("f");
hold on;
semilogy(f,module_H1);

%% 4.1.2 Synthèse du filtre passe-haut

% 1. On peut déduire la synthèse du ltre passe-haut de celle du ltre passe-bas. En eet, la
% réponse en fréquence d'un ltre passe-haut idéal peut être donnée par :
% HIP H (f ) = 1 − HIP B (f )
% où HIP B (f ) représente la réponse en fréquence du ltre passe-bas idéal de même fréquence
% de coupure. On peut donc utiliser cette expression pour en déduire la réponse impulsionnelle
% idéale d'un ltre passe-haut :
% hIP H (k) = δ(k) − hIP B (k)

% 1. Déterminer, à partir de là, la réponse impulsionnelle idéale du filtre passe-haut à implanter.
h2 = -h1;
h2((ordre-1)/2+1)=h2((ordre-1)/2+1)+1;

% 2. Implanter un filtre passe-haut de type RIF permettant de retrouver le signal x2(t) provenant
% de l'utilisateur 2.
H2 = fftshift(fft(h2,Zp));

% 3. Tracer la réponse impulsionnelle et la réponse en fréquence du filtre implanté.
figure;
subplot(2,1,1);
title("Réponse impulsionnelle du filtre passe-haut");
plot([-(ordre -1)/2:(ordre -1)/2 ],h2);
xlabel("h2(t)");
ylabel("t");

f=linspace(-Fe/2,Fe/2,Zp);
subplot(2,1,2);
title("Réponse en fréquence du filtre passe-haut");
semilogy(f,abs(H2));
xlabel("H2(f)");
ylabel("f");

% 4. Tracer, sur un même graphique, la densité spectrale de puissance du signal MF-TDMA reçu
% et le module de la réponse en fréquences du filtre implanté. 
Rx = 1/Zp * xcorr(message_signe);
Sx = fftshift(fft(Rx,Zp));

module_H2 = abs(H2);
figure;
semilogy(f, abs(Sx));
title("DSP du signal du signal MF-TDMA et |H(f)|^2");
xlabel("Sx(f) / |H(f)|^2");
ylabel("f");
hold on;
semilogy(f,module_H2);

%% 4.1.3 Filtrage

message_signe = [message_signe zeros(1,(ordre-1)/2)];

x1_tilde = filter(h1, 1, message_signe);
x2_tilde = filter(h2, 1, message_signe);

x1_tilde = x1_tilde(((ordre -1)/2)+1:end);
x2_tilde = x2_tilde(((ordre -1)/2)+1:end);

figure;
subplot(2,1,1);
title("Signal x1 après filtrage");
plot(t,x1_tilde);
xlabel("x1_tilde(t)");
ylabel("t");

subplot(2,1,2);
title("Signal x2 après filtrage");
plot(t,x2_tilde);
xlabel("x2_tilde(t)");
ylabel("t");


%% 4.2 Retour en bande de base
x1_tilde = x1_tilde.*cos(2*pi*fp1*t);
x2_tilde = x2_tilde.*cos(2*pi*fp2*t);

x1_tilde = [x1_tilde zeros(1,(ordre-1)/2)];
x2_tilde = [x2_tilde zeros(1,(ordre-1)/2)];

x1_tilde = filter(h1, 1, x1_tilde);
x2_tilde = filter(h1, 1, x2_tilde);

x1_tilde = x1_tilde(((ordre -1)/2)+1:end);
x2_tilde = x2_tilde(((ordre -1)/2)+1:end);

%% 4.3 Détection du slot utile
slots_x1 = zeros(5,length(x1_tilde)/5);
slots_x2 = zeros(5,length(x2_tilde)/5);
for i = 1:5 
    slots_x1(i,:) = x1_tilde((i-1)*Ns*Nb+1:i*Ns*Nb) ;
    slots_x2(i,:) = x2_tilde((i-1)*Ns*Nb+1:i*Ns*Nb);
end 

[~,ind1]=max(sum(abs(slots_x1),2));
[~,ind2]=max(sum(abs(slots_x2),2));

MessageRetrouve1=slots_x1(ind1,:);
MessageRetrouve2=slots_x2(ind2,:);


%% 4.4 Démodulation bande de bas
SignalFiltre=filter(ones(1,Ns),1,MessageRetrouve1) ;
SignalEchantillonne=SignalFiltre(Ns :Ns :end) ;
BitsRecuperes1=(sign(SignalEchantillonne)+1)/2 ;

disp(bin2str(BitsRecuperes1));

SignalFiltre=filter(ones(1,Ns),1,MessageRetrouve2) ;
SignalEchantillonne=SignalFiltre(Ns :Ns :end) ;
BitsRecuperes2=(sign(SignalEchantillonne)+1)/2 ;

disp(bin2str(BitsRecuperes2));