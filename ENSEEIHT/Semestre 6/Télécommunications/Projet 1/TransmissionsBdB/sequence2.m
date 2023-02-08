%% Etude des interferences entre symbole et du critere de Nyquist (Sequence 2)
clear all;
close all;

%% Etude sans canal de propagation
Fe = 24000; % fréquence d'échantillonage
Rb = 3000; % débit binaire Rb = 1/Tb
Te = 1/Fe;
nfft =1024;
figure;

%% Modulateur 1

%% Implantation du modulateur.

% Mapping : symboles binaires à moyenne nulle.
M=2;

% Filtre de mise en forme : rectangulaire de durée Ts1 = Ns1 Te

% Durée symbole en nombre d échantillons (Ts=NsTe)
Rs1 = Rb/ log2(M); % Rs = Rb / log2 (M) M=2
Ns1 = 1/ (Te * Rs1); 
Ts1 = 1/Rs1;

% Nombre de bits générés
nb_bits1=100;

% Génération de l information binaire
bits1 = randi([0,1], 1, nb_bits1);

% Mapping binaire à moyenne nulle : 0->-1, 1->1
Symboles1=2*bits1-1;

% Génération de la suite de Diracs pondérés par les symbols (suréchantillonnage)
Suite_diracs1=kron(Symboles1, [1 zeros(1,Ns1-1)]);

% Génération de la réponse impulsionnelle du filtre de mise en forme (NRZ)
h1=ones(1,Ns1);

% Filtrage de mise en forme
x1=filter(h1,1,Suite_diracs1);

%% Affichage du signal généré
subplot(2,3,1);
plot(x1);
axis([0 nb_bits1-1 -1.5 1.5]);
xlabel('Temps (s)');
ylabel('x1 : signal à la sortie du filtre de mise en forme');

%%  Tracez la densité spectrale de puissance (DSP)
%%%%%%%%%%%%%%%%%%%%% DSP de x1(t) %%%%%%%%%%%%%%%%%%%%%%
DSP1 = 1/numel(x1)*abs(fftshift(fft(x1,nfft))).^2;
f1 = linspace(-Fe/2, Fe/2, length(DSP1));
DSP1_theorique = Ts1*(sinc(f1*Ts1).^2);
subplot(2,3,4);
semilogy(f1,abs(DSP1)/max(abs(DSP1)));
hold on
semilogy(f1,abs(DSP1_theorique)/max(abs(DSP1_theorique)));
xlabel("Fréquence en Hz");
ylabel("DSP de x1");
legend('DSP Simulée de x1 ', 'DSP Théorique de x1' );
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Modulateur 2

%% Implantation du modulateur.

% Mapping : symboles binaires à moyenne nulle.
M=4;
% Filtre de mise en forme : rectangulaire de durée Ts1 = Ns1 Te

%Durée symbole en nombre d’échantillons (Ts=NsTe)
Rs2 = Rb/ log2(M); % Rs = Rb / log2 (M) M=2
Ns2 = 1/ (Te * Rs2);
Ts2 = 1/Rs2;

% Nombre de bits générés
nb_bits2=100;

%Génération de l’information binaire
bits2 = randi([0,1], 1, nb_bits2);

%Mapping Symboles 4-aires à moyenne nulle : 00->-a0, 01->a1, 11->a2 
Symboles2 = reshape(bits2, nb_bits2/2, 2);
Symboles2 = bi2de(Symboles2);
Symboles2 = (2 * Symboles2 -3)';

%Génération de la suite de Diracs pondérés par les symbols (suréchantillonnage)
Suite_diracs2=kron(Symboles2, [1 zeros(1,Ns2-1)]);

%Génération de la réponse impulsionnelle du filtre de mise en forme (NRZ)
h2=ones(1,Ns2);

%Filtrage de mise en forme
x2=filter(h2,1,[Suite_diracs2 zeros(1, length(h2))]);

%% Affichage du signal généré 
subplot(2,3,2);
plot(x2);
axis([0 nb_bits2-1 -3.5 3.5]);
xlabel('Temps (s)');
ylabel('x2 : signal à la sortie du filtre de mise en forme');

%%  Tracez la densité spectrale de puissance (DSP)
%%%%%%%%%%%%%%%%%%%%% DSP de x2(t) %%%%%%%%%%%%%%%%%%%%%%
DSP2 = 1/numel(x2)*abs(fftshift(fft(x2,nfft))).^2;
f2 = linspace(-Fe/2, Fe/2, length(DSP2));
sigma = sqrt(var(Symboles2));
DSP2_theorique = Ts2*sigma^2*(sinc(f2*Ts2).^2);
subplot(2,3,5);
semilogy(f2,abs(DSP2)/max(abs(DSP2)));
hold on
semilogy(f1,abs(DSP2_theorique)/max(abs(DSP2_theorique)));
xlabel("Fréquence en Hz");
ylabel("DSP de x2");
legend('DSP Simulée de x2 ', 'DSP Théorique de x2' );

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%% Modulateur 3

%% Implantation du modulateur.

% Mapping : symboles binaires à moyenne nulle.
M = 2;

% Filtre de mise en forme : rectangulaire de durée Ts1 = Ns1 Te

%Durée symbole en nombre d’échantillons (Ts=NsTe)
Rs3 = Rb/ log2(M); % Rs = Rb / log2 (M) M=2
Ns3 = 1/ (Te * Rs3);
Ts3 = 1/Rs3;
% Nombre de bits générés
nb_bits3=100;
%Génération de l’information binaire
bits3 = randi([0,1], 1, nb_bits1);

%Mapping binaire à moyenne nulle : 0->-1, 1->1
Symboles3=2*bits3-1;

%Génération de la suite de Diracs pondérés par les symbols (suréchantillonnage)
Suite_diracs3=kron(Symboles3, [1 zeros(1,Ns3-1)]);

%Roll-off
alpha = 0.7;

%Génération de la réponse impulsionnelle du filtre de mise en forme (NRZ)
h3 = rcosdesign(alpha, 15, Ns3);

%Filtrage de mise en forme
x3=filter(h3,1,[Suite_diracs3 zeros(1,length(h3))]);

%% Affichage du signal généré
subplot(2,3,3);
plot(x3);
axis([0 nb_bits3-1 -1.5 1.5]);
xlabel('Temps (s)');
ylabel('x3 : signal à la sortie du filtre de mise en forme');

%%  Tracez la densité spectrale de puissance (DSP)
%%%%%%%%%%%%%%%%%%%%% DSP de x3(t) %%%%%%%%%%%%%%%%%%%%%%
DSP3 = 1/numel(x3)*abs(fftshift(fft(x3,nfft))).^2;
f3 = linspace(-Fe/2, Fe/2, length(DSP3));

cond = (1-alpha)/(2*Ts3);
sigma3 = sqrt(var(Symboles3));
S1 = sigma3*Ts3;
S2 = sigma3*Ts3/4 * (1 + cos(pi*Ts3/alpha * (abs(f3) - cond))).^2;

DSP3_theorique = S1.*(abs(f3)<= cond) + S2.*(abs(f3) >= cond & abs(f3) <= (1+alpha)/(2*Ts3));
subplot(2,3,6);
semilogy(f3,abs(DSP3)/max(abs(DSP3)));
hold on
semilogy(f1,abs(DSP3_theorique)/max(abs(DSP3_theorique)));
xlabel("Fréquence en Hz");
ylabel("DSP de x3");
legend('DSP Simulée de x3 ', 'DSP Théorique de x3' );

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%% DSP sur la même courbe 
figure;
semilogy(f1,abs(DSP1));
hold on;
semilogy(f2,abs(DSP2));
semilogy(f3,abs(DSP3));
xlabel("Fréquence en Hz");
ylabel("DSP de xi");
title('Comparaison des DSP des trois modulateurs');
legend('DSP de x1', 'DSP de x2', 'DSP de x3');

%% FIN SEQUENCE 1
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Etude des interferences entre symbole et du critere de Nyquist (Sequence 2)

%% Etude sans canal de propagation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%% Demodulateur 1 %%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Filtrage de réception
hr1 = fliplr(h1);
signalfiltre1 =filter(hr1 ,1,x1);

% Affichage des Signaux filtrés
figure;
subplot(3,3,1);
plot(signalfiltre1);
title('Signal en sortie du filtre de réception');
xlabel("Temps (s)");
ylabel("Signal filtré 1");
axis([0 nb_bits1-1 -1.5 1.5]);

%% reponse impulsionnelle globale de la chaine de transmission, g
g1 = conv(h1, hr1);

% Affichage des  reponse impulsionnelle globale de la chaine de transmission, g
subplot(3,3,4);
plot(g1);
title("Réponse impulsionnelle globale");
xlabel('Temps (s)');
ylabel("g(t)");
axis([0 2*Ns1 0 10]);

%% Diagramme de l'oeil
subplot(3,3,7);
plot(reshape(signalfiltre1,Ns1,length(signalfiltre1)/Ns1));
title("Diagramme de l'oeil");

%% Echantillonnage avec n0 = Ns
x1_ech_Ns = signalfiltre1(Ns1:Ns1: length(signalfiltre1));

%% Demapping
x1_demap_Ns = x1_ech_Ns >= 0;

%% TEB
taux1_Ns = sum(bits1 ~= x1_demap_Ns);
TEB1_Ns = 100 * taux1_Ns / nb_bits1;

%% Echantillonnage avec n0 = 3
x1_ech = signalfiltre1(3:Ns1: length(signalfiltre1));

%% Demapping
x1_demap = x1_ech >= 0;

%% TEB
taux1 = sum(bits1 ~= x1_demap);
TEB1_retard3 = 100 * taux1 / nb_bits1;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%% Demodulateur 2 %%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Filtrage de réception
hr2 = fliplr(h2);
signalfiltre2 =filter(hr2 ,1,x2);
signalfiltre2_bis = signalfiltre2/Ns2;

% Affichage des Signaux filtrés
subplot(3,3,2);
plot(signalfiltre2_bis);
xlabel("Temps (s)");
ylabel("Signal filtre 2");
title('Signal en sortie du filtre de réception');
axis([0 nb_bits2-1 -3.5 3.5]);

%% Réponse impulsionnelle globale de la chaine de transmission, g
g2 = conv(h2, hr2);

% Affichage des  reponse impulsionnelle globale de la chaine de transmission, g
subplot(3,3,5);
plot(g2);
title("Réponse impulsionnelle globale");
xlabel('Temps (s)');
ylabel("g(t)");
axis([0 2*Ns2 0 30]);

%% Diagramme de l'oeil
subplot(3,3,8);
plot(reshape(signalfiltre2_bis,Ns2,length(signalfiltre2_bis)/Ns2));
title("Diagramme de l'oeil");

%% Echantillonnage avec n0 = Ns
x2_ech_Ns = signalfiltre2_bis(length(h2)+1:Ns2: length(signalfiltre2_bis));

%% Demapping
x2_demap = (0<=x2_ech_Ns & x2_ech_Ns <=2)*1 + (2<x2_ech_Ns & x2_ech_Ns<4)*3 + (0> x2_ech_Ns & x2_ech_Ns>=-2)*(-1) + (-2>x2_ech_Ns & x2_ech_Ns>-4)*(-3);
x2_demap_transpose = x2_demap';
x2_demap_2 = (x2_demap_transpose+3)/2;
x2_retour = de2bi(x2_demap_2);
bits_recus2_ns = reshape(x2_retour,1,100);

%% TEB
taux2_Ns = sum(bits2 ~= bits_recus2_ns);
TEB2_Ns = 100 * taux2_Ns / nb_bits2;

%% Echantillonnage avec n0 = 3
x2_ech = signalfiltre2_bis(length(h2)+1:3:(3*nb_bits2/2+length(h2)));

%% Demapping
x2_demap = (0<=x2_ech & x2_ech <=2)*1 + (2<x2_ech & x2_ech<4)*3 + (0> x2_ech & x2_ech>=-2)*(-1) + (-2>x2_ech & x2_ech>-4)*(-3);
x2_demap_transpose = x2_demap';
x2_demap_2 = (x2_demap_transpose+3)/2;
x2_retour = de2bi(x2_demap_2);
bits_recus2 = reshape(x2_retour,1,100);

%% TEB
taux2 = sum(bits2 ~= bits_recus2);
TEB2_retard3 = 100 * taux2 / nb_bits2;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%% Demodulateur 3 %%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Demodulateur 3
%% Filtrage de réception
hr3 = h3;
signalfiltre3 =filter(hr3 ,1,x3);

% Affichage des Signaux filtrés
subplot(3,3,3);
plot(signalfiltre3);
xlabel("Temps (s)");
ylabel("Signal filtre 3");
title('Signal en sortie du filtre de réception');
axis([0 nb_bits3-1 -1.5 1.5]);

%% reponse impulsionnelle globale de la chaine de transmission, g
g3 = conv(h3, hr3);

%% Affichage des  reponse impulsionnelle globale de la chaine de transmission, g
subplot(3,3,6);
plot(g3);
title("Réponse impulsionnelle globale");
xlabel("Temps (s)");
ylabel("g(t)");
%axis([0 2*Ns3 0 10]);

%% Diagramme de l'oeil
subplot(3,3,9);
signalfiltre3 = signalfiltre3(length(h3)+1: length(signalfiltre3));
plot(reshape(signalfiltre3,Ns3,length(signalfiltre3)/Ns3));
title("Diagramme de l'oeil");

%% Echantillonnage avec n0 = Ns
n03 = Ns3;
x3_ech_Ns = signalfiltre3(Ns3:Ns3: length(signalfiltre3));
x3_demap_Ns = x3_ech_Ns >= 0;
taux3_Ns = sum(bits3 ~= x3_demap_Ns);
TEB3_Ns = 100 * taux3_Ns / nb_bits3;

%% Echantillonnage avec n0 = 3
x3_ech = signalfiltre3(3:Ns3: length(signalfiltre3));
x3_demap = x3_ech >= 0;
taux3 = sum(bits3 ~= x3_demap);
TEB3_retard3 = 100 * taux3 / nb_bits3;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Etude avec canal de propagation sans bruit
%% Pour BW = 8000 Hz:
BW1 = 8000;
fc1 = BW1;
%% Pour BW = 1000 Hz:
BW2 = 1000;
fc2 = BW2;
%%%%%%%%%%%%%%%%%%%%%%%%%%%% 1 %%%%%%%%%%%%%%%%%%%%%%%%%%%%
figure;
N1 = 100;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Réponse impulsionnelle globale de la chaine de transmission
hc1 = (2 * fc1 /Fe) * sinc(2 * fc1 /Fe * ([-(N1-1)/2:(N1-1)/2]));
ht1 = conv(conv(h1, hc1), hr1);
subplot(2,3,1);
plot(linspace(-(N1-1)/2, (N1-1)/2, length(ht1)),ht1);
xlabel("Temps (s)");
ylabel("g(t)");
title("Réponse impulsionnelle globale g");

%% Diagramme de l'oeil
ordre = floor(N1/2);
Suite_diracs1_retard = [Suite_diracs1 zeros(1, ordre+6)]; % 6 pour que sa taille soit un multiple de 8
signalfiltre1 = filter(ht1, 1, Suite_diracs1_retard);
subplot(2,3,2);
plot(reshape(signalfiltre1, Ns1, length(signalfiltre1)/Ns1));
title("Diagramme de l'oeil en sortie du filtre de réception");

%% Réponse en fréquence des filtres 
Nf = 4096;
frequence_centre = linspace(-Fe/2, Fe/2, Nf);
H1 = fftshift(fft(h1,Nf));
Hr1 = fftshift(fft(hr1,Nf));
Hc1 = fftshift(fft(hc1,Nf));
subplot(2,3,3);
semilogy(frequence_centre, abs(H1 .* Hr1));
hold on;
semilogy(frequence_centre, abs(Hc1));
hold off;
legend("|H * Hr|", "|Hc|");
title("Réponse en fréquence des filtres");

%% TEB 
% Echantillonnage avec n0 = Ns
x1_ech_2 = signalfiltre1(ordre+7:Ns1: length(signalfiltre1));

x1_demap_2 = x1_ech_2 >= 0;
taux1_2 = sum(bits1 ~= x1_demap_2);
TEB1_BW1 = 100 * taux1_2 / nb_bits1;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%% Réponse impulsionnelle globale de la chaine de transmission
hc1 = (2 * fc2 /Fe) * sinc(2 * fc2 /Fe * ([-(N1-1)/2:(N1-1)/2]));
ht1 = conv(conv(h1, hc1), hr1);
subplot(2,3,4);
plot(linspace(-(N1-1)/2, (N1-1)/2, 114),ht1);
xlabel("temps en s");
ylabel("g(t)");
title("Réponse impulsionnelle globale g");

%% Diagramme de l'oeil
ordre = floor(N1/2);
Suite_diracs1_retard = [Suite_diracs1 zeros(1, ordre+6)];
signalfiltre1 = filter(ht1, 1, Suite_diracs1_retard);
subplot(2,3,5);
plot(reshape(signalfiltre1, Ns1, length(signalfiltre1)/Ns1));
title("Diagramme de l'oeil en sortie du filtre de réception");

%% Réponse en fréquence des filtres 
Nf = 4096;
frequence_centre = linspace(-Fe/2, Fe/2, Nf);
H1 = fftshift(fft(h1,Nf));
% Hr = fftshift(fft(h1,Nf));
Hc1 = fftshift(fft(hc1,Nf));
subplot(2,3,6);
semilogy(frequence_centre, abs(H1 .* H1));
hold on;
semilogy(frequence_centre, abs(Hc1));
hold off;
legend("|H * Hr|", "|Hc|");
title("Réponse en fréquence des filtres");

%% TEB 
% Echantillonnage avec n0 = Ns
x1_ech_2 = signalfiltre1(ordre+7:Ns1: length(signalfiltre1));
x1_demap_2 = x1_ech_2 >= 0;
taux1_2 = sum(abs(bits1 - x1_demap_2));
TEB1_BW2 = 100 * taux1_2 / nb_bits1;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%% 2 %%%%%%%%%%%%%%%%%%%%%%%%%%%%
N2 = 100;
figure;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Réponse impulsionnelle globale de la chaine de transmission
hc2 = (2 * fc1 /Fe) * sinc(2 * fc1 /Fe * ([-(N2-1)/2:(N2-1)/2]));
ht2 = conv(conv(h2, hc2), hr2);
subplot(2,3,1);
plot(linspace(-(N2-1)/2, (N2-1)/2, 130),ht2);
xlabel("temps en s");
ylabel("g(t)");
title("Réponse impulsionnelle globale g");

%% Diagramme de l'oeil
ordre = floor(N2/2);
Suite_diracs2_retard = [Suite_diracs2 zeros(1, ordre+14)];
signalfiltre2 = filter(ht2, 1, Suite_diracs2_retard);
subplot(2,3,2);
plot(reshape(signalfiltre2, Ns2, length(signalfiltre2)/Ns2));
title("Diagramme de l'oeil en sortie du filtre de réception");

%% Réponse en fréquence des filtres 
Nf = 4096;
frequence_centre = linspace(-Fe/2, Fe/2, Nf);
H2 = fftshift(fft(h2,Nf));
% Hr = fftshift(fft(h1,Nf));
Hc2 = fftshift(fft(hc2,Nf));
subplot(2,3,3);
semilogy(frequence_centre, abs(H2 .* H2));
hold on;
semilogy(frequence_centre, abs(Hc2));
hold off;
legend("|H * Hr|", "|Hc|");
title("Réponse en fréquence des filtres");

%% TEB 
% Echantillonnage avec n0 = Ns
x2_ech_2 = signalfiltre2(Ns2:Ns2: length(signalfiltre2));
x2_demap_2 = x2_ech_2 >= 0;
%taux1_2 = sum(abs(bits1 - x1_demap_2));
%TEB1_2 = 100 * taux1_2 / nb_bits1;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% BW2
%% Réponse impulsionnelle globale de la chaine de transmission
% h1 = ones(1, Ns1); Done! ligne 31
hc2 = (2 * fc2 /Fe) * sinc(2 * fc2 /Fe * ([-(N2-1)/2:(N2-1)/2]));
ht2 = conv(conv(h2, hc2), hr2);
subplot(2,3,4);
plot(linspace(-(N2-1)/2, (N2-1)/2, 130),ht2);
xlabel("temps en s");
ylabel("g(t)");
title("Réponse impulsionnelle globale g");

%% Diagramme de l'oeil
ordre = floor(N2/2);
Suite_diracs2_retard = [Suite_diracs2 zeros(1, ordre+14)];
signalfiltre2 = filter(ht2, 1, Suite_diracs2_retard);
subplot(2,3,5);
plot(reshape(signalfiltre2, Ns2, length(signalfiltre2)/Ns2));
title("Diagramme de l'oeil");

%% Réponse en fréquence des filtres 
Nf = 4096;
frequence_centre = linspace(-Fe/2, Fe/2, Nf);
H2 = fftshift(fft(h2,Nf));
% Hr = fftshift(fft(h1,Nf));
Hc2 = fftshift(fft(hc2,Nf));
subplot(2,3,6);
semilogy(frequence_centre, abs(H2 .* H2));
hold on;
semilogy(frequence_centre, abs(Hc2));
hold off;
legend("|H * Hr|", "|Hc|");
title("Réponse en fréquence des filtres");

%% TEB 
% Echantillonnage avec n0 = Ns
x2_ech_2 = signalfiltre2(Ns2:Ns2: length(signalfiltre2));
x2_demap_2 = x2_ech_2 >= 0;
%taux1_2 = sum(abs(bits1 - x1_demap_2));
%TEB1_2 = 100 * taux1_2 / nb_bits1;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%% 3 %%%%%%%%%%%%%%%%%%%%%%%%%%%%
N3 =100;
figure;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Réponse impulsionnelle globale de la chaine de transmission
% h1 = ones(1, Ns1); Done! ligne 31
hc3 = (2 * fc1 /Fe) * sinc(2 * fc1 /Fe * ([-(N3-1)/2:(N3-1)/2]));
ht3 = conv(conv(h3, hc3), hr3);
subplot(2,3,1);
plot(linspace(-(N3-1)/2, (N3-1)/2, 340),ht3);
xlabel("temps en s");
ylabel("g(t)");
title("Réponse impulsionnelle globale g");

%% Diagramme de l'oeil
ordre = floor(N3/2);
Suite_diracs3_retard = [Suite_diracs3 zeros(1, ordre+6)];
signalfiltre3 = filter(ht3, 1, Suite_diracs3_retard);
subplot(2,3,2);
plot(reshape(signalfiltre3, Ns3, length(signalfiltre3)/Ns3));
title("Diagramme de l'oeil");

%% Réponse en fréquence des filtres 
Nf = 4096;
frequence_centre = linspace(-Fe/2, Fe/2, Nf);
H3 = fftshift(fft(h3,Nf));
% Hr = fftshift(fft(h1,Nf));
Hc3 = fftshift(fft(hc3,Nf));
subplot(2,3,3);
semilogy(frequence_centre, abs(H3 .* H3));
hold on;
semilogy(frequence_centre, abs(Hc3));
hold off;
legend("|H * Hr|", "|Hc|");
title("Réponse en fréquence des filtres");

%% TEB 
no = Ns3*15;
% Echantillonnage avec n0 = Ns
x3_ech_2 = signalfiltre1(no:Ns3: length(signalfiltre3));
x3_demap_2 = x3_ech_2 >= 0;
%taux3_2 = sum(abs(bits3 - x3_demap_2));
%TEB3_2 = 100 * taux3_2 / nb_bits3;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Réponse impulsionnelle globale de la chaine de transmission
% h1 = ones(1, Ns1); Done! ligne 31
hc1 = (2 * fc2 /Fe) * sinc(2 * fc2 /Fe * ([-(N3-1)/2:(N3-1)/2]));
ht1 = conv(conv(h3, hc3), hr3);
subplot(2,3,4);
plot(linspace(-(N3-1)/2, (N3-1)/2, 340),ht3);
xlabel("temps en s");
ylabel("g(t)");
title("Réponse impulsionnelle globale g");

%% Diagramme de l'oeil
ordre = floor(N3/2);
Suite_diracs3_retard = [Suite_diracs3 zeros(1, ordre+6)];
signalfiltre3 = filter(ht3, 1, Suite_diracs3_retard);
subplot(2,3,5);
plot(reshape(signalfiltre3, Ns3, length(signalfiltre3)/Ns3));
title("Diagramme de l'oeil");

%% Réponse en fréquence des filtres 
Nf = 4096;
frequence_centre = linspace(-Fe/2, Fe/2, Nf); %%
H3 = fftshift(fft(h3,Nf));
% Hr = fftshift(fft(h1,Nf));
Hc3 = fftshift(fft(hc3,Nf));
subplot(2,3,6);
semilogy(frequence_centre, abs(H3 .* H3));
hold on;
semilogy(frequence_centre, abs(Hc3));
hold off;
legend("|H * Hr|", "|Hc|");
title("Réponse en fréquence des filtres");

%% TEB 
% Echantillonnage avec n0 = Ns
x3_ech_2 = signalfiltre1(length(signalfiltre3)/2:Ns3: length(signalfiltre3));
x3_demap_2 = x3_ech_2 >= 0;
%taux3_2 = sum(abs(bits3 - x3_demap_2));
%TEB3_2 = 100 * taux3_2 / nb_bits3;

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% FIN SEQUENCE 2 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% %%