clear all
close all
%% ------------------------ QPSK -------------------------- %

%% Génération de l%information binaire
M = 4;
n = 1000;
bits = randi([0,1], 1, n);

fp = 2000; %Hz fréquence porteuse
fe = 240000; %Hz fréquence d'échantillonnage
Te = 1/fe;
EbN0dB = [0:6];


%% Comparaison de modulations sur fréquence porteuse
alpha = 0.35;
span = 5;
sps = 10;
h = rcosdesign(alpha, span, sps);
Rb = 48000;
TEB_th = 10^(-2);

%% Etude de chaque chaine de transmission

M = 4;
Tb = 1/Rb; %période binaire
Rs = Rb/log2(M); %débit symbole
Ts = 1/Rs; %période symbole
%Ns = Ts*fe; %facteur de suréchantillonnage
Ns = 10;

%% Mapping
bits_rshp = (reshape(bits, log2(M), length(bits)/log2(M)))';
bits_rshp_intermediaire = [bits_rshp(:,2) bits_rshp(:,1)];
bits_dec = (bi2de(bits_rshp_intermediaire))';
dk2 = pskmod(bits_dec,M,pi/M); %bits <= rangement par log2(M) de bits | essayer avec mode bin
dk = 2/sqrt(2) * dk2;

% dk = pskmod(bi2de(reshape(bits,2 , n/2)')',M,pi/M,'gray');

%% Constellation
ak = real(dk);
bk = imag(dk);
figure('Name', "Constellation  QPSK (bk = f(ak)) après mapping");
plot(ak,bk,'linestyle','none','marker','o');

%% Echantillonage
a = kron(dk, [1 zeros(1,Ns-1)]); %signal suréchantillonné

%% Filtre de cos surélevé
span = 5;
sps = Ns;
h = rcosdesign(alpha, span, sps); %filtre pour la modulation en bande de base avec symboles complexes

%% Filtrage de mise en forme 
xe = filter(h,1,[a zeros(1,length(h))]);

%% DSP
[DSP,f] = pwelch(xe,[],[],[],fe,"twosided");
figure;
semilogy(DSP);
title("DSP (QPSK) sans bruit");


x = xe;

%% Filtrage de réception
z = filter(h,1,x); %signal en sortie du filtre de réception

%% Echantillonage
zm=z(length(h)+1:Ns:length(z));

%% Demmapping
bits_recus = pskdemod(zm, M, pi/M);
bits_recus22 = de2bi(bits_recus);

tmp= [bits_recus22(:,2) bits_recus22(:,1)];
bits_recus = [];
for i=1:length(bits_recus22(:,1))
    bits_recus = [bits_recus tmp(i,:)];
end

%% TEB
TEB_pbe = sum(bits~=bits_recus);
if sum(bits~=bits_recus)==0
    disp('TEB = 0 (Modulation QPSK - sans bruit)');
end
%% ------------------------------------------------------- %%

%% -------------------- Ajout du bruit ------------------- %%
%% Constellation
figure('Name', "Constellation  QPSK (bk = f(ak)) en sortie de l'échantillonage");

Puissance_recu = mean(abs(x).^2);
TEB_bruite_matrice = zeros(1,7);
TEB_theorique_matrice = zeros(1,7);
hr = h;
for i = 0:6
    EbN0 = 10^(i/10);
    sigma_n = sqrt((Puissance_recu*Ns)/(2*log2(M)*(EbN0)));
    bruit =  sigma_n * randn(1, length(x)) + j*sigma_n * randn(1, length(x));

    %% Ajout du bruit
    x_bruite = x + bruit;

    %% Filtre de réception
    z_bruite = filter(hr,1,x_bruite);

    %% Echantillonage
    zm_bruite=z_bruite(length(hr)+1:Ns:length(z_bruite));
    
    %% Constellation
    if i<6
        pos = i+1;
    else
        pos =8;
    end
    ak =real(zm);
    bk= imag(zm);
    subplot(3,3,pos);
    plot(ak,bk,'linestyle','none','marker','o');
    title('EbN0dB = ' , num2str(i));

    %bits_recus_bruite_pbe(1:2:n)=(real(zm_bruite_pbe)<0); %ak
    %bits_recus_bruite_pbe(2:2:n)=(imag(zm_bruite_pbe)<0); %bk

    %% Demapping
    bits_recus2_bruite = pskdemod(zm_bruite, M, pi/M, 'gray');
    bits_recus22_bruite = de2bi(bits_recus2_bruite);
    tmp_bruite = [bits_recus22_bruite(:,2) bits_recus22_bruite(:,1)];
    bits_recus_bruite = [];
    for j=1:length(bits_recus22_bruite(:,1))
        bits_recus_bruite = [bits_recus_bruite tmp_bruite(j,:)];
    end
   
    %% TEB
    erreur = sum(bits~=bits_recus_bruite);
    TEB_bruite = erreur/n;
    TEB_bruite_matrice(i+1) = TEB_bruite;
    if sum(bits~=bits_recus_bruite)==0
        disp('TEB = 0 (Modulation QPSK - avec bruit)');
    end
    TEB_theorique_matrice(i+1) = 2/log2(M)*qfunc(sqrt(2*log2(M)*EbN0) * sin(pi/M));

  
end
%% ------------------------------------------------------- %%

%% DSP
[DSP,f] = pwelch(x_bruite,[],[],[],fe,"twosided");
figure;
semilogy(DSP);
title("DSP (QPSK) avec bruit");

%% TEB simulé
figure;
semilogy(EbN0dB,TEB_bruite_matrice,'p--','LineWidth',3);
xlabel('E_b/N_0 (en dB)');
ylabel('TEB');
title('TEB simulé en fonction de EBN0dB ');
grid;


%% Comparaison du TEB simulé au TEB théorique de la chaine étudiée 
%TEB_theorique_matrice = qfunc(sqrt(10.^(EbN0dB/10)));

figure("Name", 'Comparaison TEB simulée et TEB théorique');
semilogy(EbN0dB,TEB_bruite_matrice,'p--','LineWidth',3);
hold on;
semilogy(EbN0dB,TEB_theorique_matrice);
legend('Simulée', 'Théorique');
xlabel('Eb/No (dB)') ;
ylabel('TEB');
title('Comparaison TEB simulée et TEB théorique');

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% FIN %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% %%