clear all;
close all;

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

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% FIN SEQUENCE 1 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% %%